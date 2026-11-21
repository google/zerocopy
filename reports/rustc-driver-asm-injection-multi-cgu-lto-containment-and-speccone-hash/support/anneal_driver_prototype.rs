// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Standalone `rustc_driver` prototype implementing:
//! 1. Post-expansion in-memory `TerminatorKind::InlineAsm` rewriting via
//!    `Config::override_queries` (`optimized_mir` and `mir_built` modes),
//!    supporting `cr_zero_drift`, `ifndef_macro`, and `multiline_pushsection`.
//! 2. `TyCtxt`-driven transitive semantic `SpecConeHash` over `Runtime(PostCleanup)`
//!    MIR, `Instance::try_resolve`, `Instance::resolve_drop_in_place`, `TyAndLayout`
//!    field offsets / niche `BackendRepr` / per-byte initialization masks, `FnAbi`,
//!    `CodegenFnAttrs`, `promoted_mir`, `required_consts`, and `ConstAllocation`.

#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_ast;
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

thread_local! {
    /// Arena-allocated `&'tcx Body<'tcx>` snapshots of `mir_drops_elaborated_and_const_checked`
    /// captured right before `optimized_mir` steals them (for instance during `--crate-type=rlib`
    /// `-C opt-level >= 1` `cross_crate_inlinable` reachability checks).
    static SAVED_POSTCLEANUP_MIR: RefCell<BTreeMap<u32, usize>> = const { RefCell::new(BTreeMap::new()) };
}

use rustc_abi::{FieldsShape, Variants};
use rustc_ast::ast::{InlineAsmTemplatePiece, InlineAsmOptions};
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId, LOCAL_CRATE};
use rustc_interface::interface;
use rustc_middle::mir::interpret::{ConstAllocation, GlobalAlloc};
use rustc_middle::mir::{
    Body, Const, ConstOperand, ConstValue, InlineAsmMacro, InlineAsmOperand, Operand, Place,
    Rvalue, StatementKind, TerminatorKind,
};
use rustc_middle::util::Providers;
use rustc_middle::ty::layout::LayoutCx;
use rustc_middle::ty::{self, Instance, InstanceKind, Ty, TyCtxt, TypeVisitableExt};
use rustc_session::Session;
use rustc_span::DUMMY_SP;
use rustc_target::spec::Arch;

// --- Minimal FIPS 180-4 SHA-256 (zero external crate dependencies) ---

struct Sha256 {
    state: [u32; 8],
    buf: [u8; 64],
    buf_len: usize,
    total_bits: u64,
}

impl Sha256 {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];

    fn new() -> Self {
        Self {
            state: [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c,
                0x1f83d9ab, 0x5be0cd19,
            ],
            buf: [0u8; 64],
            buf_len: 0,
            total_bits: 0,
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
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
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
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
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
        self.update(tag.as_bytes());
        self.update(b":");
        self.update(&(val.len() as u64).to_le_bytes());
        self.update(val.as_bytes());
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

// --- Part 1: Post-Expansion MIR InlineAsm Rewriter (`override_queries`) ---

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
            // Range [200_000_000, 899_999_999]: starts with digit 2..8 so Intel-syntax
            // MASM lexer never treats `<id>b` as a binary literal.
            labels[i] = 200_000_000 + (raw % 700_000_000) + (i as u64);
        }
        let distinct = labels[0] != labels[1]
            && labels[0] != labels[2]
            && labels[0] != labels[3]
            && labels[1] != labels[2]
            && labels[1] != labels[3]
            && labels[2] != labels[3];
        let mut collides = false;
        for l in labels {
            let s = l.to_string();
            if user_text.contains(&s) {
                collides = true;
                break;
            }
        }
        if distinct && !collides {
            return labels;
        }
        salt += 1;
    }
}

fn rewrite_body_inline_asm<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId, body: &mut Body<'tcx>, mode: &str) {
    let nonce = session_nonce();
    let cmt = target_comment_prefix(&tcx.sess.target.arch);
    let crate_name = tcx.crate_name(LOCAL_CRATE);
    let def_path_hash = tcx.def_path_hash(def_id.to_def_id());

    for (bb_idx, bb_data) in body.basic_blocks.as_mut_preserves_cfg().iter_enumerated_mut() {
        let Some(term) = bb_data.terminator.as_mut() else { continue };
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

        // Compute deterministic collision-free 64-bit site_id from (crate, DefPathHash, bb).
        let mut sh = Sha256::new();
        sh.update_tag("crate", crate_name.as_str());
        sh.update_tag("def_path_hash", &format!("{def_path_hash:?}"));
        sh.update(& (bb_idx.index() as u64).to_le_bytes());
        let site_digest = sh.finalize();
        let site_id = u64::from_le_bytes(site_digest[0..8].try_into().unwrap()) & 0x7fff_ffff_ffff_ffff;

        let mut user_concat = String::new();
        for p in template.iter() {
            if let InlineAsmTemplatePiece::String(s) = p {
                user_concat.push_str(s);
            }
        }
        let lower_check = user_concat.to_ascii_lowercase();
        for forbidden in [".macro", ".altmacro", ".rept", ".irp", ".irpc"] {
            if lower_check.contains(forbidden) {
                tcx.dcx().span_err(
                    term.source_info.span,
                    format!("anneal-driver: assembler directive `{forbidden}` forbidden in verified asm"),
                );
                return;
            }
        }

        let [l_s, l_e, l_d, l_de] = derive_disjoint_labels(&nonce, site_id, &user_concat);

        // Classify operands into `.asciz` register/const entries vs `.quad` symbol/label relocs.
        // Note: `InlineAsmMacro::NakedAsm` only supports `Const` and `Sym*` operands.
        let is_naked = matches!(asm_macro, InlineAsmMacro::NakedAsm);
        let mut desc_pieces: Vec<InlineAsmTemplatePiece> = Vec::new();
        let mut reloc_indices: Vec<usize> = Vec::new();

        // Determine separator (\r for cr_zero_drift, \n for multiline_pushsection / ifndef_macro).
        let sep = if mode == "cr_zero_drift" { "\r" } else { "\n" };

        desc_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
            "{nonce}|site={site_id}"
        ))));

        for (op_idx, op) in operands.iter().enumerate() {
            match op {
                InlineAsmOperand::In { .. } if !is_naked => {
                    desc_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!("|in{op_idx}="))));
                    desc_pieces.push(InlineAsmTemplatePiece::Placeholder {
                        operand_idx: op_idx,
                        modifier: None,
                        span: DUMMY_SP,
                    });
                }
                InlineAsmOperand::Out { reg, place, .. } if !is_naked => {
                    match place {
                        Some(_) => {
                            desc_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
                                "|out{op_idx}="
                            ))));
                            desc_pieces.push(InlineAsmTemplatePiece::Placeholder {
                                operand_idx: op_idx,
                                modifier: None,
                                span: DUMMY_SP,
                            });
                        }
                        None => {
                            // Explicit register clobbers (`out("r10") _`) may not have an `op_idx`
                            // entry in `rustc_codegen_llvm/src/asm.rs:88-98`; record statically.
                            desc_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
                                "|clob{op_idx}={reg}"
                            ))));
                        }
                    }
                }
                InlineAsmOperand::InOut { .. } if !is_naked => {
                    desc_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
                        "|inout{op_idx}="
                    ))));
                    desc_pieces.push(InlineAsmTemplatePiece::Placeholder {
                        operand_idx: op_idx,
                        modifier: None,
                        span: DUMMY_SP,
                    });
                }
                InlineAsmOperand::Const { .. } => {
                    desc_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
                        "|const{op_idx}="
                    ))));
                    desc_pieces.push(InlineAsmTemplatePiece::Placeholder {
                        operand_idx: op_idx,
                        modifier: None,
                        span: DUMMY_SP,
                    });
                }
                InlineAsmOperand::SymFn { .. } | InlineAsmOperand::SymStatic { .. } => {
                    reloc_indices.push(op_idx);
                }
                InlineAsmOperand::Label { .. } if !is_naked => {
                    // Do not duplicate `Label` placeholders when avoid-callbr-dup is needed unless
                    // emitting `.quad` reloc; check whether `asm.rs:248` supports `.quad {lbl}`.
                    reloc_indices.push(op_idx);
                }
                _ => {}
            }
        }

        let mut new_pieces: Vec<InlineAsmTemplatePiece> = Vec::new();

        if mode == "ifndef_macro" && !is_naked && reloc_indices.is_empty() {
            // Inline per-CGU `.ifndef` macro definition using `\@` expansion counter.
            let mac_name = format!("__aw_{}_{}", &nonce[..12], site_id);
            new_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
                ".ifndef {mac_name}\n\
                 .macro {mac_name}\n\
                 .pushsection .anneal.asm_sites,\"e\",@progbits\n\
                 .quad {l_s}b, {l_e}b, {site_id}, {l_d}b, {l_de}b - {l_d}b, 0\n\
                 .popsection\n\
                 .endm\n\
                 .set {mac_name}, 1\n\
                 .endif\n\
                 {l_s}:\n"
            ))));
            new_pieces.extend(template.iter().cloned());
            new_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
                "\n{l_e}:\n\
                 .pushsection .anneal.asm_descs,\"e\",@progbits\n\
                 {l_d}: .asciz \""
            ))));
            new_pieces.extend(desc_pieces);
            new_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
                "\"\n{l_de}: .popsection\n{mac_name}"
            ))));
        } else {
            // Universal `cr_zero_drift` (`sep == "\r"`) or `multiline_pushsection` (`sep == "\n"`).
            // Under `cr_zero_drift`, `.space 0 <cmt>\r` resets `AtInsnStart = false` in
            // `TargetInstrInfo::getInlineAsmLength` (`TargetInstrInfo.cpp:120-146`) while
            // `AsmLexer.cpp:313, 898-906` treats `\r` as `EndOfStatement`, yielding exact
            // 0-byte `getInlineAsmLength` overhead across x86_64, aarch64, and riscv64gc.
            if mode == "cr_zero_drift" {
                new_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
                    ".space 0 {cmt}\r{l_s}:\n"
                ))));
            } else {
                new_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!("{l_s}:\n"))));
            }
            new_pieces.extend(template.iter().cloned());
            if mode == "cr_zero_drift" {
                new_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
                    "\r.space 0 {cmt}\r{l_e}:\r\
                     .pushsection .anneal.asm_descs,\"e\",@progbits\r\
                     {l_d}: .asciz \""
                ))));
            } else {
                new_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
                    "\n{l_e}:\n\
                     .pushsection .anneal.asm_descs,\"e\",@progbits\n\
                     {l_d}: .asciz \""
                ))));
            }
            new_pieces.extend(desc_pieces);
            let n_rel = reloc_indices.len();
            new_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
                "\"{sep}{l_de}: .popsection{sep}\
                 .pushsection .anneal.asm_sites,\"e\",@progbits{sep}\
                 .quad {l_s}b, {l_e}b, {site_id}, {l_d}b, {l_de}b - {l_d}b, {n_rel}"
            ))));
            for r_idx in reloc_indices {
                new_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!("{sep}.quad "))));
                // On x86_64 Intel syntax (`!ATT_SYNTAX`), `sym` in `.quad` prints cleanly via `:c`
                // (automatically emitted by `asm.rs` for Sym/Label).
                let _ = options.contains(InlineAsmOptions::ATT_SYNTAX);
                new_pieces.push(InlineAsmTemplatePiece::Placeholder {
                    operand_idx: r_idx,
                    modifier: None,
                    span: DUMMY_SP,
                });
            }
            new_pieces.push(InlineAsmTemplatePiece::String(Cow::Owned(format!(
                "{sep}.popsection"
            ))));
        }

        let new_line_count = new_pieces
            .iter()
            .map(|p| match p {
                InlineAsmTemplatePiece::String(s) => s.matches('\n').count(),
                InlineAsmTemplatePiece::Placeholder { .. } => 0,
            })
            .sum::<usize>()
            + 1;
        let span_fill = line_spans.first().copied().unwrap_or(term.source_info.span);
        let new_spans: Vec<_> = (0..new_line_count).map(|_| span_fill).collect();

        *template = tcx.arena.alloc_from_iter(new_pieces);
        *line_spans = tcx.arena.alloc_from_iter(new_spans);
    }
}

fn custom_optimized_mir<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> &'tcx Body<'tcx> {
    if std::env::var("ANNEAL_SPECCONE_FN").is_ok() {
        let steal = tcx.mir_drops_elaborated_and_const_checked(def_id);
        if !steal.is_stolen() {
            let saved: &'tcx Body<'tcx> = tcx.arena.alloc(steal.borrow().clone());
            SAVED_POSTCLEANUP_MIR.with(|m| {
                m.borrow_mut()
                    .insert(def_id.local_def_index.as_u32(), saved as *const Body<'tcx> as usize);
            });
        }
    }
    let orig = (rustc_interface::DEFAULT_QUERY_PROVIDERS.queries.optimized_mir)(tcx, def_id);
    let mode = std::env::var("ANNEAL_ASM_WRAP_MODE").unwrap_or_else(|_| "off".to_string());
    if mode == "off" || mode == "mir_built_cr" {
        return orig;
    }
    let mut cloned = orig.clone();
    rewrite_body_inline_asm(tcx, def_id, &mut cloned, &mode);
    tcx.arena.alloc(cloned)
}

extern crate rustc_data_structures;

fn custom_mir_built<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> &'tcx rustc_data_structures::steal::Steal<Body<'tcx>> {
    let orig = (rustc_interface::DEFAULT_QUERY_PROVIDERS.queries.mir_built)(tcx, def_id);
    let mode = std::env::var("ANNEAL_ASM_WRAP_MODE").unwrap_or_else(|_| "off".to_string());
    if mode != "mir_built_cr" {
        return orig;
    }
    let mut cloned = orig.borrow().clone();
    rewrite_body_inline_asm(tcx, def_id, &mut cloned, "cr_zero_drift");
    tcx.arena.alloc(rustc_data_structures::steal::Steal::new(cloned))
}

fn override_queries(_sess: &Session, providers: &mut Providers) {
    let mode = std::env::var("ANNEAL_ASM_WRAP_MODE").unwrap_or_else(|_| "off".to_string());
    if mode == "mir_built_cr" {
        providers.queries.mir_built = custom_mir_built;
    }
    if mode != "off" && mode != "mir_built_cr" || std::env::var("ANNEAL_SPECCONE_FN").is_ok() {
        providers.queries.optimized_mir = custom_optimized_mir;
    }
}

// --- Part 2: `TyCtxt`-Driven Semantic `SpecConeHash` Collector ---

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
    queue: VecDeque<Instance<'tcx>>,
    visited_instances: BTreeSet<String>,
    instance_digests: BTreeMap<String, String>,
    type_digests: BTreeMap<String, String>,
    alloc_digests: BTreeMap<String, String>,
}

impl<'tcx> SpecConeCollector<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
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

    fn canonical_instance_key(&self, inst: Instance<'tcx>) -> String {
        format!("{inst:?}|{}", self.canonical_def_id(inst.def_id()))
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
                // A byte in a union is guaranteed initialized iff every union field covers and
                // initializes that byte (so `MaybeUninit<T>` with `uninit: ()` yields all-false).
                let mut mask = vec![true; sz];
                for idx in 0..count.get() {
                    let f_layout = layout.field(&cx, idx);
                    let f_mask = self.compute_init_byte_mask(typing_env, f_layout.ty, depth + 1);
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
                    let elem_mask = self.compute_init_byte_mask(typing_env, elem_ty, depth + 1);
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
                        let f_mask = self.compute_init_byte_mask(typing_env, f_ty, depth + 1);
                        let base = off.bytes_usize();
                        for (i, &bit) in f_mask.iter().enumerate() {
                            if base + i < sz {
                                mask[base + i] |= bit;
                            }
                        }
                    }
                    mask
                }
                Variants::Multiple { tag, tag_field, variants, .. } => {
                    let mut mask = vec![true; sz];
                    if variants.is_empty() {
                        return vec![false; sz];
                    }
                    for v_idx in variants.indices() {
                        let v_layout = layout.for_variant(&cx, v_idx);
                        let mut v_mask = vec![false; sz];
                        if let FieldsShape::Arbitrary { offsets: v_offs, .. } = &v_layout.fields {
                            for (f_idx, off) in v_offs.iter_enumerated() {
                                let f_ty = v_layout.field(&cx, f_idx.index()).ty;
                                let f_m = self.compute_init_byte_mask(typing_env, f_ty, depth + 1);
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

    fn record_type_and_layout(&mut self, typing_env: ty::TypingEnv<'tcx>, ty: Ty<'tcx>) {
        let ty = self.tcx.erase_and_anonymize_regions(ty);
        let key = format!("{ty:?}");
        if self.type_digests.contains_key(&key) {
            return;
        }
        // Insert sentinel first to break recursive ADT pointer cycles.
        self.type_digests.insert(key.clone(), String::new());

        let mut h = Sha256::new();
        h.update_tag("ty", &key);
        if let ty::Adt(adt_def, args) = *ty.kind() {
            h.update_tag("adt_def", &self.canonical_def_id(adt_def.did()));
            h.update_tag("adt_repr", &format!("{:?}", adt_def.repr()));
            for f in adt_def.all_fields() {
                let f_ty = self
                    .tcx
                    .normalize_erasing_regions(typing_env, f.ty(self.tcx, args));
                h.update_tag("field", &format!("{}:{f_ty:?}", f.name));
                self.record_type_and_layout(typing_env, f_ty);
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
            let mask_str: String = init_mask.iter().map(|&b| if b { 'I' } else { 'U' }).collect();
            h.update_tag("init_byte_mask", &mask_str);
        }
        self.type_digests.insert(key, Sha256::hex(&h.finalize()));
    }

    fn hash_const_alloc(&mut self, typing_env: ty::TypingEnv<'tcx>, alloc: ConstAllocation<'tcx>) -> String {
        let inner = alloc.inner();
        let len = inner.len();
        let bytes = inner.inspect_with_uninit_and_ptr_outside_interpreter(0..len);
        let mut h = Sha256::new();
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
            GlobalAlloc::Memory(mem) => format!("mem:{}", self.hash_const_alloc(typing_env, mem)),
            GlobalAlloc::Function { instance } => {
                self.enqueue_instance(instance);
                format!("fn:{}", self.canonical_instance_key(instance))
            }
            GlobalAlloc::Static(def_id) => {
                let mut sh = Sha256::new();
                sh.update_tag("static_def", &self.canonical_def_id(def_id));
                if let Ok(val) = self.tcx.eval_static_initializer(def_id) {
                    sh.update_tag("static_val", &self.hash_const_alloc(typing_env, val));
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
                rustc_middle::mir::interpret::Scalar::Int(i) => format!("int:{i:?}"),
                rustc_middle::mir::interpret::Scalar::Ptr(ptr, size) => {
                    let (prov, offset) = ptr.prov_and_relative_offset();
                    let target = self.record_global_alloc(typing_env, prov.alloc_id());
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
                if let Ok(Some(resolved)) = Instance::try_resolve(self.tcx, typing_env, uv.def, uv.args) {
                    let _ = self.canonical_instance_key(resolved);
                }
            }
        }

        if let ty::FnDef(fn_def_id, fn_args) = *mono_ty.kind() {
            #[cfg(not(anneal_rustc_1_98))]
            let fn_args = fn_args.skip_binder();
            if let Ok(Some(callee)) = Instance::try_resolve(self.tcx, typing_env, fn_def_id, fn_args) {
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
        op: &Operand<'tcx>,
    ) -> String {
        match op {
            Operand::Copy(p) => format!("copy({})", self.hash_place(inst, typing_env, p)),
            Operand::Move(p) => format!("move({})", self.hash_place(inst, typing_env, p)),
            Operand::Constant(c) => format!("const({})", self.hash_const_operand(inst, typing_env, c)),
            other => format!("op_other({other:?})"),
        }
    }

    fn hash_place(
        &mut self,
        inst: Instance<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        place: &Place<'tcx>,
    ) -> String {
        let mut s = format!("_{}", place.local.as_usize());
        for elem in place.projection.iter() {
            match elem {
                rustc_middle::mir::ProjectionElem::Field(f, ty) => {
                    let m_ty = inst.instantiate_mir_and_normalize_erasing_regions(
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
        s
    }

    fn hash_mir_body(
        &mut self,
        inst: Instance<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        body: &Body<'tcx>,
        h: &mut Sha256,
    ) {
        // Local declarations (types + mutability ONLY; excludes `var_debug_info` and source `Span`s
        // so comments, line shifts, and alpha-renaming of local variable names are 100% invariant).
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
                &format!("_{}:{:?}:{m_ty:?}", local_idx.as_usize(), decl.mutability),
            );
        }

        // Also hash `body.required_consts()` (catches constants folded/extracted by PromoteTemps).
        if let Some(req_consts) = body.required_consts.as_ref() {
            for rc in req_consts {
                let c_str = self.hash_const_operand(inst, typing_env, rc);
                h.update_tag("required_const", &c_str);
            }
        }

        for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
            h.update_tag("bb", &format!("bb{}:cleanup={}", bb.index(), bb_data.is_cleanup));
            for stmt in &bb_data.statements {
                match &stmt.kind {
                    StatementKind::Assign(box_pair) => {
                        let (lhs, rhs) = &**box_pair;
                        let lhs_s = self.hash_place(inst, typing_env, lhs);
                        let rhs_s = self.hash_rvalue(inst, typing_env, rhs);
                        h.update_tag("assign", &format!("{lhs_s} = {rhs_s}"));
                    }
                    StatementKind::SetDiscriminant { place, variant_index } => {
                        let p_s = self.hash_place(inst, typing_env, place);
                        h.update_tag("set_disc", &format!("{p_s} := {}", variant_index.as_usize()));
                    }
                    StatementKind::StorageLive(l) => {
                        h.update_tag("storage_live", &format!("_{}", l.as_usize()));
                    }
                    StatementKind::StorageDead(l) => {
                        h.update_tag("storage_dead", &format!("_{}", l.as_usize()));
                    }
                    StatementKind::PlaceMention(p) => {
                        let p_s = self.hash_place(inst, typing_env, p);
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
                        h.update_tag("term", &format!("goto->bb{}", target.index()));
                    }
                    TerminatorKind::SwitchInt { discr, targets, .. } => {
                        let d_s = self.hash_operand(inst, typing_env, discr);
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
                    TerminatorKind::Unreachable => h.update_tag("term", "unreachable"),
                    TerminatorKind::UnwindResume => h.update_tag("term", "unwind_resume"),
                    TerminatorKind::UnwindTerminate(reason) => {
                        h.update_tag("term", &format!("unwind_terminate({reason:?})"));
                    }
                    TerminatorKind::Drop { place, target, unwind, replace, .. } => {
                        let p_s = self.hash_place(inst, typing_env, place);
                        let raw_ty = place.ty(&body.local_decls, self.tcx).ty;
                        let drop_ty = inst.instantiate_mir_and_normalize_erasing_regions(
                            self.tcx,
                            typing_env,
                            early_bind(self.tcx, raw_ty),
                        );
                        self.record_type_and_layout(typing_env, drop_ty);
                        let drop_glue = Instance::resolve_drop_glue(self.tcx, drop_ty);
                        let has_nontrivial_drop = drop_ty.needs_drop(self.tcx, typing_env);
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
                    TerminatorKind::Call { func, args, destination, target, unwind, .. } => {
                        let f_s = self.hash_operand(inst, typing_env, func);
                        let a_s: Vec<String> = args
                            .iter()
                            .map(|a| self.hash_operand(inst, typing_env, &a.node))
                            .collect();
                        let dst_s = self.hash_place(inst, typing_env, destination);
                        let tgt_s = target.map(|b| format!("bb{}", b.index())).unwrap_or_else(|| "!".into());
                        h.update_tag(
                            "term_call",
                            &format!("{dst_s} = {f_s}({}) -> {tgt_s} unw={unwind:?}", a_s.join(",")),
                        );
                    }
                    TerminatorKind::Assert { cond, expected, target, unwind, .. } => {
                        let c_s = self.hash_operand(inst, typing_env, cond);
                        h.update_tag(
                            "term_assert",
                            &format!("assert({c_s} == {expected}) -> bb{} unw={unwind:?}", target.index()),
                        );
                    }
                    TerminatorKind::InlineAsm { asm_macro, template, operands, options, targets, unwind, .. } => {
                        let t_s = InlineAsmTemplatePiece::to_string(template);
                        h.update_tag(
                            "term_asm",
                            &format!("{asm_macro:?}:{t_s}:opts={options:?}:ops={}:tgts={targets:?}:unw={unwind:?}", operands.len()),
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
        rv: &Rvalue<'tcx>,
    ) -> String {
        match rv {
            Rvalue::Use(op, _) => format!("use({})", self.hash_operand(inst, typing_env, op)),
            Rvalue::Repeat(op, c) => {
                let m_c = inst.instantiate_mir_and_normalize_erasing_regions(
                    self.tcx,
                    typing_env,
                    early_bind(self.tcx, *c),
                );
                format!("repeat({};{m_c:?})", self.hash_operand(inst, typing_env, op))
            }
            Rvalue::Ref(_, bk, p) => format!("ref({bk:?},{})", self.hash_place(inst, typing_env, p)),
            Rvalue::RawPtr(kind, p) => format!("rawptr({kind:?},{})", self.hash_place(inst, typing_env, p)),
            Rvalue::BinaryOp(op, box_ops) => format!(
                "binop({op:?},{},{})",
                self.hash_operand(inst, typing_env, &box_ops.0),
                self.hash_operand(inst, typing_env, &box_ops.1)
            ),
            Rvalue::UnaryOp(op, x) => format!("unop({op:?},{})", self.hash_operand(inst, typing_env, x)),
            Rvalue::Cast(kind, op, ty) => {
                let m_ty = inst.instantiate_mir_and_normalize_erasing_regions(
                    self.tcx,
                    typing_env,
                    early_bind(self.tcx, *ty),
                );
                self.record_type_and_layout(typing_env, m_ty);
                format!("cast({kind:?},{},{m_ty:?})", self.hash_operand(inst, typing_env, op))
            }
            Rvalue::Aggregate(box_kind, fields) => {
                let f_s: Vec<String> = fields
                    .iter()
                    .map(|f| self.hash_operand(inst, typing_env, f))
                    .collect();
                format!("agg({box_kind:?},[{}])", f_s.join(","))
            }
            Rvalue::Discriminant(p) => format!("disc({})", self.hash_place(inst, typing_env, p)),
            Rvalue::CopyForDeref(p) => format!("deref_copy({})", self.hash_place(inst, typing_env, p)),
            other => format!("rv_other({other:?})"),
        }
    }

    fn process_instance(&mut self, inst: Instance<'tcx>) {
        let key = self.canonical_instance_key(inst);
        let def_id = inst.def_id();
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let mut h = Sha256::new();
        h.update_tag("instance", &key);
        h.update_tag("def_kind", &format!("{:?}", self.tcx.def_kind(def_id)));

        // FnAbi (calling convention, argument/return PassModes, unwind semantics) + CodegenFnAttrs.
        if !inst.args.has_non_region_param() {
            if let Ok(fn_abi) = self
                .tcx
                .fn_abi_of_instance(typing_env.as_query_input((inst, ty::List::empty())))
            {
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
        h.update_tag("target_features", &format!("{:?}", cg_attrs.target_features));
        h.update_tag("codegen_flags", &format!("{:?}", cg_attrs.flags));
        h.update_tag("inline_attr", &format!("{:?}", cg_attrs.inline));

        // Obtain MIR body: prefer un-inlined `Runtime(PostCleanup)` MIR (`mir_drops_elaborated_and_const_checked`)
        // for local items so helper calls, promoted consts, and drop terminators are explicitly preserved,
        // falling back to `instance_mir` for compiler shims (`DropGlue`) and foreign crate items.
        match inst.def {
            InstanceKind::Item(d) if d.is_local() => {
                let local_d = d.expect_local();
                if matches!(
                    self.tcx.def_kind(d),
                    DefKind::Fn | DefKind::AssocFn | DefKind::Closure
                ) {
                    let steal = self.tcx.mir_drops_elaborated_and_const_checked(local_d);
                    if !steal.is_stolen() {
                        let body = steal.borrow();
                        self.hash_mir_body(inst, typing_env, &body, &mut h);
                    } else if let Some(ptr) = SAVED_POSTCLEANUP_MIR
                        .with(|m| m.borrow().get(&local_d.local_def_index.as_u32()).copied())
                    {
                        // SAFETY: `ptr` was allocated in `self.tcx.arena` during this exact
                        // compiler session (`custom_optimized_mir`) before `.steal()`.
                        let body: &'tcx Body<'tcx> = unsafe { &*(ptr as *const Body<'tcx>) };
                        self.hash_mir_body(inst, typing_env, body, &mut h);
                    } else {
                        let body = self.tcx.optimized_mir(d);
                        self.hash_mir_body(inst, typing_env, body, &mut h);
                    }
                    let promos = self.tcx.promoted_mir(local_d);
                    for (p_idx, p_body) in promos.iter_enumerated() {
                        h.update_tag("promoted_idx", &format!("{}", p_idx.as_usize()));
                        self.hash_mir_body(inst, typing_env, p_body, &mut h);
                    }
                }
            }
            InstanceKind::Intrinsic(_) | InstanceKind::Virtual(_, _) => {
                h.update_tag("shim_or_intrinsic", &format!("{:?}", inst.def));
            }
            _ => {
                if self.tcx.is_mir_available(def_id) || !matches!(inst.def, InstanceKind::Item(_)) {
                    let body = self.tcx.instance_mir(inst.def);
                    self.hash_mir_body(inst, typing_env, body, &mut h);
                }
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

        let mut master = Sha256::new();
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

        // Emit structured JSON without external serde crate.
        let esc = |s: &str| -> String {
            s.replace('\\', "\\\\")
                .replace('"', "\\\"")
                .replace('\n', "\\n")
        };
        let inst_keys: Vec<String> = self
            .instance_digests
            .keys()
            .map(|k| format!("\"{}\"", esc(k)))
            .collect();
        let type_keys: Vec<String> = self
            .type_digests
            .keys()
            .map(|k| format!("\"{}\"", esc(k)))
            .collect();
        format!(
            "{{\n  \"spec_cone_hash\": \"{cone_hash}\",\n  \"num_instances\": {},\n  \"num_types\": {},\n  \"num_allocs\": {},\n  \"instances\": [{}],\n  \"types\": [{}]\n}}\n",
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

    fn after_analysis<'tcx>(&mut self, _compiler: &interface::Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        if tcx.dcx().has_errors().is_some() {
            return Compilation::Continue;
        }
        if let Ok(target_fn) = std::env::var("ANNEAL_SPECCONE_FN") {
            if !target_fn.is_empty() {
                let mut found: Option<LocalDefId> = None;
                for local_def_id in tcx.hir_body_owners() {
                    if tcx.def_path_str(local_def_id.to_def_id()).ends_with(&target_fn)
                        && matches!(
                            tcx.def_kind(local_def_id.to_def_id()),
                            DefKind::Fn | DefKind::AssocFn
                        )
                    {
                        if tcx.def_path_str(local_def_id.to_def_id()) == target_fn || found.is_none() {
                            found = Some(local_def_id);
                        }
                    }
                }
                if let Some(root) = found {
                    let mut collector = SpecConeCollector::new(tcx);
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

fn main() -> ExitCode {
    rustc_driver::catch_with_exit_code(|| {
        let mut args: Vec<String> = std::env::args().collect();
        // Support `RUSTC_WRAPPER` invocation (`driver <rustc-path> <args...>`).
        if args.len() >= 2 && (args[1].ends_with("rustc") || args[1].contains("/rustc")) {
            args.remove(1);
        }
        SAVED_POSTCLEANUP_MIR.with(|m| m.borrow_mut().clear());
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
    })
}
