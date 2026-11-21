#!/usr/bin/env python3
"""Check the upstream pins and the source anchors that the report cites.

Step 1 (pins). For every subject of `../REPORT.json` that has a `repository` and a `revision`,
ask the GitHub API (through the `gh` CLI) for that commit and require that the full 40-hex SHA it
returns equals the pinned revision.

Step 2 (anchors). Fetch each cited file at its pinned revision from `raw.githubusercontent.com`
and check a list of anchors: literal strings that must be present (their 1-based line numbers are
recorded) or must be absent. A file may also be required not to exist (HTTP 404).

The anchors are the statements about upstream source that the report relies on; if one of them
fails at a newer revision, the corresponding finding has to be re-read rather than assumed.

Usage:

    python3 support/audit_sources.py --out support/source_audit.json

`--gh` replaces the `gh` command (for example to add authentication options). The script exits
non-zero if a pin does not resolve to itself or an anchor has an unexpected status.
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import http.client
import json
import re
import shlex
import subprocess
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent

RUST = "rust-lang/rust"
OLD = "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65"   # rustc 1.98.0-nightly, the executed toolchain
NEW = "3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1"   # rustc 1.102.0-nightly, source only
ANNEAL = "joshlf/anneal"
ANNEAL_REV = "c131b320eeeb26ef692e5afd5ec8db49ee518613"

BOTH = (OLD, NEW)

# (repository, revisions, path, expected HTTP status, anchors)
# An anchor is (label, literal string, expected) with expected one of "present" / "absent".
FILES = [
    (RUST, BOTH, "src/version", 200, []),
    (RUST, BOTH, "compiler/rustc_allocator/src/lib.rs", 404, []),
    (RUST, BOTH, "compiler/rustc_ast/src/expand/allocator.rs", 200, [
        ("marker name", 'pub const NO_ALLOC_SHIM_IS_UNSTABLE: &str = "__rust_no_alloc_shim_is_unstable_v2";', "present"),
        ("global prefix", 'format!("__rust_{base}")', "present"),
        ("default prefix", 'format!("__rdl_{base}")', "present"),
        ("method table", "pub static ALLOCATOR_METHODS: &[AllocatorMethod] = &[", "present"),
        ("no should_panic symbol", "should_panic", "absent"),
        ("no OomStrategy", "OomStrategy", "absent"),
    ]),
    (RUST, BOTH, "compiler/rustc_builtin_macros/src/global_allocator.rs", 200, [
        ("internal symbol attribute", "self.cx.attr_word(sym::rustc_std_internal_symbol, self.span)", "present"),
        ("allocator attribute", "sym::alloc => sym::rustc_allocator,", "present"),
        ("deallocator attribute", "sym::dealloc => sym::rustc_deallocator,", "present"),
        ("layout rebuilt from size and alignment", "sym::from_size_alignment_unchecked", "present"),
        ("function names", "global_fn_name(method.name)", "present"),
    ]),
    (RUST, BOTH, "compiler/rustc_builtin_macros/src/alloc_error_handler.rs", 200, [
        ("generated handler", "// unsafe fn __rust_alloc_error_handler(size: usize, align: usize) -> ! {", "present"),
    ]),
    (RUST, BOTH, "compiler/rustc_codegen_ssa/src/base.rs", 200, [
        ("shim contents", "pub fn allocator_shim_contents(", "present"),
        ("methods only for the default allocator", "if kind == AllocatorKind::Default {", "present"),
        ("handler only for the default handler", "if tcx.alloc_error_handler_kind(()).unwrap() == AllocatorKind::Default {", "present"),
        ("shim module", "backend.codegen_allocator(tcx, &llmod_id, &allocator_shim_contents(tcx, kind));", "present"),
    ]),
    (RUST, BOTH, "compiler/rustc_codegen_llvm/src/allocator.rs", 200, [
        ("marker comment", "// __rust_no_alloc_shim_is_unstable_v2", "present"),
        ("marker definition", "&mangle_internal_symbol(tcx, NO_ALLOC_SHIM_IS_UNSTABLE),", "present"),
        ("wrapper source name", "let from_name = mangle_internal_symbol(tcx, &global_fn_name(method.name));", "present"),
        ("wrapper target name", "let to_name = mangle_internal_symbol(tcx, &default_fn_name(method.name));", "present"),
        ("tail call", "llvm::LLVMSetTailCall(ret, TRUE);", "present"),
    ]),
    (RUST, BOTH, "compiler/rustc_codegen_llvm/src/attributes.rs", 200, [
        ("alloc family", 'llvm::CreateAttrStringValue(llcx, "alloc-family", "__rust_alloc")', "present"),
        ("free kind", "to_add.push(llvm::CreateAllocKindAttr(cx.llcx, AllocKindFlags::Free));", "present"),
        ("alloc size", "to_add.push(llvm::CreateAllocSizeAttr(cx.llcx, 0));", "present"),
    ]),
    (RUST, BOTH, "compiler/rustc_symbol_mangling/src/v0.rs", 200, [
        ("internal symbol mangling", "pub fn mangle_internal_symbol", "present"),
        ("pseudo crate", "__rustc", "present"),
    ]),
    (RUST, BOTH, "library/alloc/src/alloc.rs", 200, [
        ("alloc declaration", "fn __rust_alloc(size: usize, align: Alignment) -> *mut u8;", "present"),
        ("dealloc declaration", "fn __rust_dealloc(ptr: NonNull<u8>, size: usize, align: Alignment);", "present"),
        ("marker declaration", "fn __rust_no_alloc_shim_is_unstable_v2();", "present"),
        ("marker call", "        __rust_no_alloc_shim_is_unstable_v2();", "present"),
        ("marker rationale", "// Make sure we don't accidentally allow omitting the allocator shim in", "present"),
        ("zero size allocate", "0 => Ok(layout.dangling_ptr().cast_slice(0)),", "present"),
        ("zero size deallocate", "        if layout.size() != 0 {", "present"),
        ("handler declaration", "fn __rust_alloc_error_handler(size: usize, align: usize) -> !;", "present"),
        ("default handler", "pub unsafe fn __rdl_alloc_error_handler(size: usize, _align: usize) -> ! {", "present"),
        ("no should_panic symbol", "should_panic", "absent"),
        ("no exchange_malloc", "exchange_malloc", "absent"),
        ("no box_free", "box_free", "absent"),
    ]),
    (RUST, (OLD,), "library/alloc/src/boxed.rs", 200, [
        ("box_new_uninit is not const", "\nfn box_new_uninit(layout: Layout) -> *mut u8 {", "present"),
        ("box_new_uninit const", "const fn box_new_uninit(layout: Layout) -> *mut u8 {", "absent"),
    ]),
    (RUST, (NEW,), "library/alloc/src/boxed.rs", 200, [
        ("box_new_uninit const", "\nconst fn box_new_uninit(layout: Layout) -> *mut u8 {", "present"),
        ("box_new_uninit zero size return", "        return layout.dangling_ptr().as_ptr();", "present"),
    ]),
    (RUST, BOTH, "library/alloc/src/boxed.rs", 200, [
        ("box_new_uninit allocates through Global", "    match Global.allocate(layout) {", "present"),
        ("box_new_uninit failure", "        Err(_) => handle_alloc_error(layout),", "present"),
        ("box_new_uninit not MIR-inlined", "#[rustc_no_mir_inline]", "present"),
        ("Box::new allocates", "let ptr = box_new_uninit(<T as SizedTypeProperties>::LAYOUT) as *mut T;", "present"),
        ("Box::new no-panic comment", "// Nothing below can panic so we do not have to worry about deallocating `ptr`.", "present"),
        ("Box::new stores", "unsafe { core::intrinsics::write_via_move(ptr, x) };", "present"),
        ("Box::new transmutes", "unsafe { mem::transmute(ptr) }", "present"),
        ("new_uninit transmutes", "unsafe { mem::transmute(box_new_uninit(<T as SizedTypeProperties>::LAYOUT)) }", "present"),
        ("vec helper", "fn box_assume_init_into_vec_unsafe<T, const N: usize>(", "present"),
        ("Drop impl", "unsafe impl<#[may_dangle] T: ?Sized, A: Allocator> Drop for Box<T, A> {", "present"),
        ("Drop impl comment", "// the T in the Box is dropped by the compiler before the destructor is run", "present"),
        ("Drop impl layout", "Layout::for_value_raw(ptr.as_ptr())", "present"),
        ("Drop impl deallocate", "self.1.deallocate(From::from(ptr.cast()), layout);", "present"),
        ("no rustc_box", "rustc_box", "absent"),
        ("no exchange_malloc", "exchange_malloc", "absent"),
        ("no box_free", "box_free", "absent"),
    ]),
    (RUST, BOTH, "library/alloc/src/intrinsics.rs", 200, [
        ("write_box_via_move", "pub fn write_box_via_move<T>(b: Box<MaybeUninit<T>>, x: T) -> Box<MaybeUninit<T>>;", "present"),
    ]),
    (RUST, BOTH, "library/alloc/src/macros.rs", 200, [
        ("vec literal helper", "$crate::boxed::box_assume_init_into_vec_unsafe(", "present"),
        ("vec literal store", "$crate::intrinsics::write_box_via_move($crate::boxed::Box::new_uninit(), [$($x),+])", "present"),
    ]),
    (RUST, BOTH, "library/core/src/intrinsics/mod.rs", 200, [
        ("write_via_move", "pub const unsafe fn write_via_move<T>(ptr: *mut T, value: T);", "present"),
    ]),
    (RUST, BOTH, "library/core/src/alloc/layout.rs", 200, [
        ("dangling_ptr", "pub const fn dangling_ptr(&self) -> NonNull<u8> {", "present"),
        ("dangling address is the alignment", "NonNull::without_provenance(self.align.as_nonzero_usize())", "present"),
        ("maximum size", "unsafe { unchecked_sub(isize::MAX as usize + 1, alignment.as_usize()) }", "present"),
        ("alignment field", "    align: Alignment,", "present"),
    ]),
    (RUST, BOTH, "library/core/src/alloc/global.rs", 200, [
        ("alloc zero size", "/// `layout` must have non-zero size. Attempting to allocate for a zero-sized `layout` will", "present"),
        ("dealloc live block", "/// * `ptr` is a block of memory currently allocated via this allocator and,", "present"),
        ("dealloc same layout", "/// * `layout` is the same layout that was used to allocate that block of", "present"),
        ("no unwinding", "/// * It's undefined behavior if global allocators unwind.", "present"),
    ]),
    (RUST, (OLD,), "library/core/src/alloc/global.rs", 200, [
        ("allocations may not happen", "/// * You must not rely on allocations actually happening, even if there are explicit", "present"),
        ("no statement about merging", "merge multiple allocation operations", "absent"),
    ]),
    (RUST, (NEW,), "library/core/src/alloc/global.rs", 200, [
        ("allocator may be skipped", "/// - Allocation functions may non-deterministically entirely skip the underlying allocator, e.g. if the", "present"),
        ("allocations may be merged", "///   also merge multiple allocation operations into one, as long as it can also adjust all", "present"),
        ("allocations may not happen", "/// The first point means that you cannot rely on global allocations actually happening, even if", "present"),
        ("only the global functions may free", "///   freed by invoking [`dealloc`] or [`realloc`]. In particular, passing a pointer to such an", "present"),
    ]),
    (RUST, BOTH, "library/std/src/alloc.rs", 200, [
        ("std handler attribute", "#[alloc_error_handler]", "present"),
        ("std handler", "pub fn rust_oom(layout: Layout) -> ! {", "present"),
        ("failure message", 'rtprintpanic!("memory allocation of {} bytes failed\\n", layout.size());', "present"),
        ("abort", "        crate::process::abort()", "present"),
        ("default alloc", 'pub unsafe extern "C" fn __rdl_alloc(size: usize, align: usize) -> *mut u8 {', "present"),
    ]),
    (RUST, BOTH, "library/std/src/lib.rs", 200, [
        ("std provides the default allocator", "#![default_lib_allocator]", "present"),
    ]),
    (RUST, BOTH, "compiler/rustc_metadata/src/creader.rs", 200, [
        ("allocator kind decision", "fn inject_allocator_crate(&mut self, tcx: TyCtxt<'_>, krate: &ast::Crate) {", "present"),
        ("global kind", "self.allocator_kind = Some(AllocatorKind::Global);", "present"),
        ("default kind", "self.allocator_kind = Some(AllocatorKind::Default);", "present"),
    ]),
    (RUST, BOTH, "library/alloc/src/raw_vec/mod.rs", 200, [
        ("zero-sized capacity", "if elem_size == 0 { usize::MAX } else { self.cap.as_inner() }", "present"),
    ]),
    (RUST, BOTH, "compiler/rustc_mir_build/src/builder/expr/into.rs", 200, [
        ("write_via_move lowering", "// `write_via_move(ptr, val)` becomes `*ptr = val` but without any dropping.", "present"),
        ("write_box_via_move lowering", "sym::write_box_via_move => {", "present"),
    ]),
    (RUST, BOTH, "compiler/rustc_mir_transform/src/lower_intrinsics.rs", 200, [
        ("already lowered", "// `write_via_move` is already lowered during MIR building.", "present"),
    ]),
    (RUST, BOTH, "compiler/rustc_mir_transform/src/elaborate_drop.rs", 200, [
        ("box contents", "fn open_drop_for_box_contents(", "present"),
        ("box special case", "            let destructor_block = if adt.is_box() {", "present"),
        ("contents before destructor", "// we need to drop the inside of the box before running the destructor", "present"),
        ("deref subpath", "let interior_path = self.elaborator.deref_subpath(self.path);", "present"),
        ("destructor call", "fn destructor_call_block_sync(&mut self, succ: BasicBlock, unwind: Unwind) -> BasicBlock {", "present"),
        ("no box_free", "box_free", "absent"),
    ]),
    (RUST, (OLD,), "compiler/rustc_mir_transform/src/elaborate_box_derefs.rs", 200, [
        ("cast kind", "CastKind::Transmute,", "present"),
        ("no dedicated cast kind", "BoxDerefTransmute", "absent"),
    ]),
    (RUST, (NEW,), "compiler/rustc_mir_transform/src/elaborate_box_derefs.rs", 200, [
        ("dedicated cast kind", "Rvalue::Cast(CastKind::BoxDerefTransmute, Operand::Copy(field_place), ptr_ty),", "present"),
    ]),
    (RUST, BOTH, "compiler/rustc_mir_transform/src/elaborate_box_derefs.rs", 200, [
        ("purpose", "//! This pass transforms derefs of Box into a deref of the pointer inside Box.", "present"),
    ]),
    (RUST, BOTH, "compiler/rustc_mir_transform/src/lib.rs", 200, [
        ("drop elaboration pass", "        &elaborate_drops::ElaborateDrops,", "present"),
        ("box deref pass", "        &elaborate_box_derefs::ElaborateBoxDerefs,", "present"),
    ]),
    (RUST, BOTH, "compiler/rustc_middle/src/mir/syntax.rs", 200, [
        ("Rvalue", "pub enum Rvalue<'tcx> {", "present"),
        ("no ShallowInitBox", "ShallowInitBox", "absent"),
        ("no NullaryOp", "NullaryOp", "absent"),
    ]),
    (RUST, BOTH, "compiler/rustc_const_eval/src/interpret/memory.rs", 200, [
        ("layout check", '"incorrect layout on deallocation: {alloc_id} has size {size} and alignment {align}, but gave size {size_found} and alignment {align_found}",', "present"),
    ]),
    (RUST, BOTH, "src/tools/miri/src/shims/alloc.rs", 200, [
        ("zero size check", 'throw_ub_format!("creating allocation with size 0");', "present"),
        ("request check", "fn check_rust_alloc_request(&self, size: u64, align: u64) -> InterpResult<'tcx> {", "present"),
    ]),
    (RUST, BOTH, "src/tools/miri/src/shims/foreign_items.rs", 200, [
        ("marker shim", ".mangle_internal_symbol(NO_ALLOC_SHIM_IS_UNSTABLE) => {", "present"),
        ("marker rationale", "// This is a no-op shim that only exists to prevent making the allocator shims", "present"),
    ]),
    (RUST, BOTH, "compiler/rustc_feature/src/removed.rs", 200, [
        ("box_syntax removal note", '(removed, box_syntax, "1.70.0", Some(49733), Some("replaced with `#[rustc_box]`"), 108471),', "present"),
    ]),
    (RUST, BOTH, "src/doc/rustc-dev-guide/src/lang-items.md", 200, [
        ("stale mention of exchange_malloc", "exchange_malloc", "present"),
        ("stale mention of box_free", "box_free", "present"),
    ]),
    (ANNEAL, (ANNEAL_REV,), "trusted/lean/Trusted/MirAst.lean", 200, [
        ("Rvalue", "inductive Rvalue where", "present"),
        ("unsupported rvalue", "- `.unsupported` represents all other `Rvalue` variants (`Repeat`,", "present"),
        ("terminators", "inductive TerminatorKind where", "present"),
        ("unsupported terminators", "(`UnwindTerminate`, `Drop`, indirect `Call`, `TailCall`, `Yield`,", "present"),
        ("quoted rustc revision", "8144389c895da997dbdecaa635e41d6a50be6ffd", "present"),
        ("struct types are unsupported", "non-fieldless-enum `Adt`", "present"),
        ("no ShallowInitBox", "ShallowInitBox", "absent"),
    ]),
    (ANNEAL, (ANNEAL_REV,), "trusted/lean/Trusted/MirSemantics.lean", 200, [
        ("caller memory must be empty", "  else if !q.callerMem.allocations.isEmpty then", "present"),
        ("calls fault as unsupported", "  | .unwindResume | .assert _ _ _ _ _ | .call _ _ _ _ _ | .unsupported =>", "present"),
        ("no heap allocation primitive", "__rust_alloc", "absent"),
    ]),
]


def fetch_with_curl(url: str):
    """(HTTP status, body or None) using `curl`; (None, None) if curl is missing or fails."""
    try:
        proc = subprocess.run(["curl", "-sS", "-m", "60", "--retry", "3", "-w", "\n%{http_code}", url],
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    except OSError:
        return None, None
    body, _, code = proc.stdout.rpartition(b"\n")
    code = code.decode().strip()
    if code.isdigit() and code != "000":
        return int(code), body if code == "200" else None
    return None, None


def fetch(url: str):
    """(HTTP status, body bytes or None). Network errors are retried; an HTTP status is final."""
    status, body = fetch_with_curl(url)
    if status is not None:
        return status, body
    for attempt in range(4):
        try:
            with urllib.request.urlopen(urllib.request.Request(url), timeout=60) as resp:
                return resp.status, resp.read()
        except urllib.error.HTTPError as exc:
            return exc.code, None
        except (OSError, http.client.HTTPException):
            time.sleep(1 + attempt)
    return None, None


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--gh", default="gh", help="command used to reach the GitHub API")
    ap.add_argument("--out", default=str(HERE / "source_audit.json"))
    args = ap.parse_args(argv)
    gh = shlex.split(args.gh)

    report = json.loads((HERE.parent / "REPORT.json").read_text())
    ok = True
    commits = []
    pinned = set()
    for subject in report["subjects"]:
        ident = subject["identity"]
        repo, rev = ident.get("repository"), ident.get("revision")
        if not repo or not rev:
            continue
        pinned.add((repo, rev))
        entry = {"repository": repo, "pinned_revision": rev,
                 "is_40_hex": bool(re.fullmatch(r"[0-9a-f]{40}", rev))}
        proc = subprocess.run(gh + ["api", f"repos/{repo}/commits/{rev}"],
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            data = json.loads(proc.stdout.decode("utf-8", "replace"))
            entry["api_sha"] = data.get("sha")
            entry["committer_date"] = data.get("commit", {}).get("committer", {}).get("date")
            entry["subject_line"] = (data.get("commit", {}).get("message") or "").splitlines()[0][:100]
        except ValueError:
            entry["api_sha"] = None
            entry["error"] = "no JSON from the API call"
        entry["verified"] = entry["is_40_hex"] and entry.get("api_sha") == rev
        ok = ok and entry["verified"]
        commits.append(entry)

    files = []
    cache = {}
    for repo, revs, path, expected_status, anchors in FILES:
        for rev in revs:
            if (repo, rev) not in pinned:
                ok = False
                files.append({"repository": repo, "revision": rev, "path": path,
                              "error": "revision is not a subject of REPORT.json"})
                continue
            key = (repo, rev, path)
            if key not in cache:
                cache[key] = fetch(f"https://raw.githubusercontent.com/{repo}/{rev}/{path}")
            status, body = cache[key]
            entry = {"repository": repo, "revision": rev, "path": path,
                     "expected_status": expected_status, "status": status, "anchors": []}
            file_ok = status == expected_status
            if body is not None:
                text = body.decode("utf-8", "replace")
                entry["sha256"] = hashlib.sha256(body).hexdigest()
                entry["lines"] = text.count("\n")
                if path == "src/version":
                    entry["content"] = text.strip()
                for label, needle, expected in anchors:
                    lines = []
                    start = 0
                    while True:
                        i = text.find(needle, start)
                        if i < 0:
                            break
                        # A needle that starts with a newline anchors the line that follows it.
                        lines.append(text.count("\n", 0, i) + 1 + (1 if needle.startswith("\n") else 0))
                        start = i + 1
                    found = "present" if lines else "absent"
                    entry["anchors"].append({"label": label, "text": needle.strip("\n"), "expected": expected,
                                             "found": found, "lines": lines[:8], "occurrences": len(lines)})
                    file_ok = file_ok and found == expected
            entry["passed"] = file_ok
            ok = ok and file_ok
            files.append(entry)

    receipt = {
        "schema": "source-audit/1",
        "generated_on": datetime.date.today().isoformat(),
        "commits": commits,
        "files": files,
        "summary": {
            "commits": len(commits),
            "file_checks": len(files),
            "anchors": sum(len(f.get("anchors", [])) for f in files),
            "failed": [f"{f['repository']}@{f['revision'][:12]}:{f['path']}" for f in files if not f.get("passed")],
        },
        "passed": bool(ok),
    }
    Path(args.out).write_text(json.dumps(receipt, indent=1, sort_keys=True) + "\n")
    for c in commits:
        print(f"{'ok  ' if c['verified'] else 'FAIL'} {c['repository']}@{c['pinned_revision']} ({c.get('committer_date')})")
    for f in files:
        if not f.get("passed"):
            print("FAIL", f["repository"], f["revision"][:12], f["path"], f.get("status"),
                  [a for a in f.get("anchors", []) if a["found"] != a["expected"]])
    print(f"file checks: {len(files)}, anchors: {receipt['summary']['anchors']}, failed: {len(receipt['summary']['failed'])}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
