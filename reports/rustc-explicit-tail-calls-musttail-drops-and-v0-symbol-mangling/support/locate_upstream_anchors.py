#!/usr/bin/env python3
"""Locate the rustc source regions this report cites, at any rust-lang/rust commit.

For each (file, anchor text) pair the script reports the 1-based line of the first
line containing the anchor and a short SHA-256 of the region that starts there, so
two commits can be compared region by region without a checkout: equal digests mean
the region is byte-identical, a missing line means the anchor text no longer exists.

Usage:
    # fetch each file from raw.githubusercontent.com at the given commits
    python3 locate_upstream_anchors.py <40-hex-sha> [<40-hex-sha> ...] > anchors.json

    # or read from local trees laid out as <root>/<sha>/<path in the repository>
    python3 locate_upstream_anchors.py --local-root DIR <sha> [<sha> ...] > anchors.json

Standard library only (network mode falls back to the `curl` executable when
`urllib` cannot reach the host). The digests are over the anchor line and the following
`region_lines - 1` lines exactly as they appear in the file.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import urllib.request
from pathlib import Path

REPO = "rust-lang/rust"
C = "compiler/"

# (repository path, anchor text, number of lines in the digested region, what it is)
ANCHORS = [
    (C + "rustc_middle/src/mir/syntax.rs", "    /// Tail call.", 29,
     "TerminatorKind::TailCall definition and doc comment"),
    (C + "rustc_middle/src/mir/terminator.rs", "| TailCall { .. }", 2,
     "TailCall listed among terminators without successors"),
    (C + "rustc_hir_typeck/src/expr.rs", "fn check_expr_become(", 25,
     "type check of `become`: return type must match without coercion"),
    (C + "rustc_mir_build/src/check_tail_calls.rs", "if caller_sig.abi() != callee_sig.abi() {", 3,
     "caller/callee ABI equality check"),
    (C + "rustc_mir_build/src/check_tail_calls.rs",
     "if !callee_sig.abi().supports_guaranteed_tail_call() {", 3,
     "ABI must support guaranteed tail calls"),
    (C + "rustc_mir_build/src/check_tail_calls.rs",
     "if caller_sig.inputs_and_output != callee_sig.inputs_and_output", 3,
     "caller/callee signature equality check (first three lines)"),
    (C + "rustc_mir_build/src/check_tail_calls.rs", "`become` is not allowed in closures", 1,
     "closure rejection diagnostic"),
    (C + "rustc_abi/src/extern_abi.rs", "pub fn supports_guaranteed_tail_call(self) -> bool {", 45,
     "per-ABI tail-call support table"),
    (C + "rustc_abi/src/extern_abi.rs", "    RustTail,", 1,
     "`extern \"tail\"` ABI variant (absent before it was introduced)"),
    (C + "rustc_feature/src/unstable.rs", "explicit_tail_calls,", 1,
     "feature gate status of explicit_tail_calls"),
    (C + "rustc_feature/src/unstable.rs", "rust_tail_cc,", 1,
     "feature gate of the `extern \"tail\"` ABI (absent before it was introduced)"),
    (C + "rustc_mir_build/src/builder/expr/stmt.rs", "ExprKind::Become { value } => {", 37,
     "MIR building of `become`"),
    (C + "rustc_mir_build/src/builder/scope.rs", "pub(crate) fn break_for_tail_call(", 109,
     "scheduling of the caller's drops before the tail call"),
    (C + "rustc_mir_build/src/builder/scope.rs", "assert!(local.index() > self.arg_count);", 1,
     "StorageDead is only emitted for non-argument locals"),
    (C + "rustc_borrowck/src/lib.rs", "TerminatorKind::TailCall { func, args, fn_span: _ } => {", 6,
     "borrow check: tail call consumes its operands"),
    (C + "rustc_borrowck/src/lib.rs", "| TerminatorKind::TailCall { .. }", 2,
     "borrow check: tail call invalidates locals like a return"),
    (C + "rustc_mir_transform/src/inline.rs",
     "} else if let TerminatorKind::TailCall { .. } = term.kind {", 4,
     "MIR inliner refuses callee bodies containing a tail call"),
    (C + "rustc_mir_transform/src/inline.rs",
     "// FIXME(explicit_tail_calls): figure out if we can inline tail calls", 2,
     "MIR inliner only considers `Call` terminators as call sites"),
    (C + "rustc_mir_transform/src/inline.rs",
     "check_inline::is_inline_valid_on_body(tcx, callee_body)?;", 1,
     "per-call-site use of the body validity check"),
    (C + "rustc_mir_transform/src/check_inline.rs", "pub(super) fn is_inline_valid_on_body", 14,
     "body validity check shared with #[rustc_force_inline]"),
    (C + "rustc_codegen_ssa/src/mir/block.rs", "if kind == CallKind::Tail {", 4,
     "codegen dispatches tail calls to the backend's tail_call"),
    (C + "rustc_codegen_ssa/src/mir/block.rs", "let mut tail_call_temporaries = vec![];", 1,
     "indirect arguments are copied through temporaries for tail calls"),
    (C + "rustc_codegen_ssa/src/mir/block.rs",
     "mir::TerminatorKind::TailCall { ref func, ref args, fn_span } => self", 13,
     "codegen of the TailCall terminator"),
    (C + "rustc_codegen_llvm/src/builder.rs", "fn tail_call(", 1,
     "LLVM backend tail_call entry"),
    (C + "rustc_codegen_llvm/src/builder.rs",
     "llvm::LLVMSetTailCallKind(call, llvm::TailCallKind::MustTail);", 6,
     "call marked musttail, followed by ret"),
    (C + "rustc_const_eval/src/interpret/call.rs", "pub(super) fn init_fn_tail_call(", 52,
     "interpreter: pop the frame, push the callee with the popped return continuation"),
    (C + "rustc_const_eval/src/interpret/step.rs",
     "TailCall { ref func, ref args, fn_span: _ } => {", 20,
     "interpreter: asserts the frame index is unchanged by a tail call"),
    (C + "rustc_session/src/config.rs", "pub fn get_symbol_mangling_version(&self)", 3,
     "default symbol mangling version"),
    (C + "rustc_session/src/config.rs",
     "// Check for unstable values of `-C symbol-mangling-version`.", 26,
     "which mangling versions need -Z unstable-options"),
    (C + "rustc_symbol_mangling/src/lib.rs",
     "SymbolManglingVersion::V0 => v0::mangle(tcx, instance, instantiating_crate, false),", 1,
     "dispatch to the v0 mangler"),
    (C + "rustc_symbol_mangling/src/v0.rs", "fn print_backref(&mut self, i: usize)", 5,
     "backreference emission"),
    (C + "rustc_symbol_mangling/src/v0.rs", "if let Some(&i) = self.types.get(&ty) {", 4,
     "type cache lookup before printing a type"),
    (C + "rustc_symbol_mangling/src/v0.rs", "self.types.insert(ty, start);", 1,
     "type cache insertion keyed by start offset"),
    (C + "rustc_symbol_mangling/src/v0.rs", "if let Some(&i) = self.paths.get(&(def_id, args)) {", 4,
     "path cache lookup"),
    (C + "rustc_symbol_mangling/src/legacy.rs", "fn get_symbol_hash<", 57,
     "legacy mangling: what the hash covers"),
    (C + "rustc_symbol_mangling/src/legacy.rs", "fn finish(mut self, hash: Hash64)", 6,
     "legacy mangling: `17h` + 16 hex digits suffix"),
]


def load(sha: str, path: str, local_root: str | None) -> str | None:
    if local_root:
        p = Path(local_root) / sha / path
        return p.read_text() if p.exists() else None
    url = f"https://raw.githubusercontent.com/{REPO}/{sha}/{path}"
    try:
        with urllib.request.urlopen(url, timeout=60) as resp:
            return resp.read().decode("utf-8")
    except Exception as exc:
        # Some environments only let the `curl` executable through their proxy.
        curl = shutil.which("curl")
        if curl:
            proc = subprocess.run([curl, "-fsS", "-m", "60", url], capture_output=True, text=True)
            if proc.returncode == 0:
                return proc.stdout
            exc = f"{exc}; curl: {proc.stderr.strip()}"
        # Report the failure; never substitute a guess.
        print(f"warning: could not fetch {url}: {exc}", file=sys.stderr)
        return None


def locate(text: str | None, anchor: str, region_lines: int) -> dict:
    if text is None:
        return {"line": None, "region_sha256_16": None, "file_available": False}
    lines = text.splitlines()
    for idx, line in enumerate(lines):
        if anchor in line:
            region = "\n".join(lines[idx: idx + region_lines])
            digest = hashlib.sha256(region.encode("utf-8")).hexdigest()[:16]
            return {"line": idx + 1, "region_sha256_16": digest, "file_available": True}
    return {"line": None, "region_sha256_16": None, "file_available": True}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--local-root", default=None)
    ap.add_argument("shas", nargs="+")
    args = ap.parse_args()
    for sha in args.shas:
        if len(sha) != 40 or any(c not in "0123456789abcdef" for c in sha):
            ap.error(f"not a full 40-hex commit id: {sha}")

    cache: dict[tuple[str, str], str | None] = {}
    rows = []
    for path, anchor, region_lines, what in ANCHORS:
        per_commit = {}
        for sha in args.shas:
            if (sha, path) not in cache:
                cache[(sha, path)] = load(sha, path, args.local_root)
            per_commit[sha] = locate(cache[(sha, path)], anchor, region_lines)
        digests = {v["region_sha256_16"] for v in per_commit.values()}
        rows.append({
            "path": path,
            "anchor": anchor,
            "what": what,
            "region_lines": region_lines,
            "identical_across_commits": len(digests) == 1 and None not in digests,
            "commits": per_commit,
        })
    json.dump({"repository": REPO, "commits": args.shas, "anchors": rows}, sys.stdout, indent=2)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
