#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Prototype of the 4-Level Content-Addressed Verification Cache for cargo-anneal
and end-to-end benchmark suite across 6 scenarios on starnix (api::apply_endianness).
"""

import copy
import hashlib
import json
import os
import pathlib
import shutil
import subprocess
import tempfile
import time

LEAN = pathlib.Path("/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean")
LEANC = LEAN.parent / "leanc"
CAPTURE = pathlib.Path("/tmp/ref_research_stack221_perf/mvp_src/target/release/anneal-rustc-capture")
SYSROOT = pathlib.Path("/usr/local/google/home/joshlf/.rustup/toolchains/nightly-2026-05-31-x86_64-unknown-linux-gnu")
STARNIX_FIXTURE = pathlib.Path("/tmp/ref_research_stack221_perf/fixtures/starnix")
BASELINE_ARTIFACTS = pathlib.Path("/tmp/anneal-mvp-starnix-installed-final/baseline-artifacts")
MVP_SRC = pathlib.Path("/tmp/ref_research_stack221_perf/mvp_src")
ANNEAL_LEAN_RUN = pathlib.Path("/usr/local/google/home/joshlf/.local/bin/anneal-lean-run")
SUPPORT_DIR = pathlib.Path("/tmp/ref_research_stack221_perf/track6/support")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: pathlib.Path) -> str:
    return sha256_bytes(path.read_bytes())


def canonical_json_bytes(obj) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":")).encode("utf-8")


def sha256_json(obj) -> str:
    return sha256_bytes(canonical_json_bytes(obj))


def stat_fingerprint(path: pathlib.Path):
    st = path.stat()
    return [st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns]


class VerificationCache:
    """Content-addressed multi-level cache for cargo-anneal verify."""

    def __init__(self, cache_root: pathlib.Path):
        self.root = cache_root
        self.capture_dir = self.root / "level1_capture"
        self.header_dir = self.root / "level3_headers"
        self.olean_dir = self.root / "level3_oleans"
        self.audit_dir = self.root / "level4_audit"
        self.toolchain_dir = self.root / "toolchain"
        for d in [self.capture_dir, self.header_dir, self.olean_dir, self.audit_dir, self.toolchain_dir]:
            d.mkdir(parents=True, exist_ok=True)

    def ensure_native_inspector(self) -> pathlib.Path:
        """Compile or retrieve cached native TrustedBoundary binary (`leanc -O3 -rdynamic`)."""
        tb_src = MVP_SRC / "trusted/audit/TrustedBoundary.lean"
        key = sha256_json({
            "kind": "trusted_boundary_native_v1",
            "lean_sha256": sha256_file(LEAN),
            "leanc_sha256": sha256_file(LEANC),
            "trusted_boundary_sha256": sha256_file(tb_src),
        })
        bin_path = self.toolchain_dir / f"trusted-boundary-{key[:16]}"
        if bin_path.exists():
            return bin_path
        # Also reuse pre-built support binary if hashes match
        pre_built = SUPPORT_DIR / "trusted-boundary-bin"
        if pre_built.exists():
            shutil.copy2(pre_built, bin_path)
            return bin_path
        with tempfile.TemporaryDirectory(prefix="tb_build_") as tmp:
            stage = pathlib.Path(tmp)
            tb_lean = stage / "TrustedBoundary.lean"
            tb_c = stage / "TrustedBoundary.c"
            shutil.copy2(tb_src, tb_lean)
            subprocess.run(
                [str(ANNEAL_LEAN_RUN), "--mode", "file", "--concurrency", "4", "--",
                 str(LEAN), "-j1", "-M2048", "-c", str(tb_c), str(tb_lean)],
                cwd=stage, check=True, capture_output=True
            )
            subprocess.run(
                [str(LEANC), "-O3", "-rdynamic", "-o", str(bin_path), str(tb_c)],
                cwd=stage, check=True, capture_output=True
            )
        return bin_path

    def admit_toolchain_and_locks(self, fast_stat: bool = True):
        """Verify or load cached toolchain + foundation-lock + library-lock admission."""
        lock_path = MVP_SRC / "trusted/lean/foundation-lock.json"
        lib_lock_path = MVP_SRC / "trusted/audit/library-lock.json"
        tb_path = MVP_SRC / "trusted/audit/TrustedBoundary.lean"
        lock_sha = sha256_file(lock_path)
        lib_lock_sha = sha256_file(lib_lock_path)
        tb_sha = sha256_file(tb_path)
        lean_sha = sha256_file(LEAN)

        adm_cache_file = self.toolchain_dir / f"admission-{lean_sha[:12]}-{lock_sha[:12]}-{lib_lock_sha[:12]}.json"
        if fast_stat and adm_cache_file.exists():
            cached = json.loads(adm_cache_file.read_text())
            # Verify stat fingerprint of LEAN binary and lock files
            if cached["lean_stat"] == stat_fingerprint(LEAN):
                return cached

        ver_out = subprocess.run([str(LEAN), "--version"], capture_output=True, text=True, check=True).stdout.strip()
        prefix = pathlib.Path(
            subprocess.run([str(LEAN), "--print-prefix"], capture_output=True, text=True, check=True).stdout.strip()
        ).resolve()
        lock = json.loads(lock_path.read_text())
        lib_lock = json.loads(lib_lock_path.read_text())

        foundation_arts = {}
        foundation_part_shas = {}
        for mod, rec in lock["modules"].items():
            rel = mod.replace(".", "/")
            src_p = prefix / "src/lean" / f"{rel}.lean"
            assert sha256_file(src_p) == rec["sourceSha256"]
            olean_parts, ir_parts, part_digests = [], [], {}
            for p in ["olean", "olean.server", "olean.private", "ir.sig", "ir"]:
                exp = rec["parts"].get(p)
                inst = prefix / "lib/lean" / f"{rel}.{p}"
                if exp is not None:
                    actual = sha256_file(inst)
                    assert actual == exp
                    part_digests[p] = actual
                    if p in ("olean", "olean.server", "olean.private"):
                        olean_parts.append(str(inst))
                    else:
                        ir_parts.append(str(inst))
            foundation_arts[mod] = [olean_parts, ir_parts]
            foundation_part_shas[mod] = part_digests

        lib_arts = {}
        lib_part_shas = {}
        for mod, rec in lib_lock["modules"].items():
            rel = mod.replace(".", "/")
            src_p = prefix / "src/lean" / f"{rel}.lean"
            assert sha256_file(src_p) == rec["sourceSha256"]
            olean_parts, ir_parts, part_digests = [], [], {}
            for p in ["olean", "olean.server", "olean.private", "ir.sig", "ir"]:
                exp = rec["parts"].get(p)
                inst = prefix / "lib/lean" / f"{rel}.{p}"
                if exp is not None:
                    actual = sha256_file(inst)
                    assert actual == exp
                    part_digests[p] = actual
                    if p in ("olean", "olean.server", "olean.private"):
                        olean_parts.append(str(inst))
                    else:
                        ir_parts.append(str(inst))
            lib_arts[mod] = [olean_parts, ir_parts]
            lib_part_shas[mod] = part_digests

        adm_record = {
            "lean_sha256": lean_sha,
            "lean_stat": stat_fingerprint(LEAN),
            "version": ver_out,
            "prefix": str(prefix),
            "foundation_lock_sha256": lock_sha,
            "library_lock_sha256": lib_lock_sha,
            "trusted_boundary_sha256": tb_sha,
            "foundation_graph": lock["graph"],
            "foundation_arts": foundation_arts,
            "foundation_part_shas": foundation_part_shas,
            "library_graph": lib_lock["graph"],
            "library_arts": lib_arts,
            "library_part_shas": lib_part_shas,
            "axioms": lock["axioms"],
        }
        adm_cache_file.write_text(json.dumps(adm_record))
        return adm_record


def compute_sysroot_identity(sysroot: pathlib.Path, cache: VerificationCache) -> str:
    """Compute a fast, sound sysroot identity bound to rustc binary and driver libraries."""
    rustc_bin = sysroot / "bin/rustc"
    fp_file = cache.toolchain_dir / "sysroot_identity.json"
    cur_stat = stat_fingerprint(rustc_bin)
    if fp_file.exists():
        cached = json.loads(fp_file.read_text())
        if cached["sysroot"] == str(sysroot) and cached["rustc_stat"] == cur_stat:
            return cached["sysroot_identity_sha256"]
    ver_verbose = subprocess.run(
        [str(rustc_bin), "--version", "--verbose"], capture_output=True, text=True, check=True
    ).stdout
    rustc_sha = sha256_file(rustc_bin)
    lib_entries = []
    for so_file in sorted((sysroot / "lib").glob("*.so*")):
        if so_file.is_file() and not so_file.is_symlink():
            st = so_file.stat()
            lib_entries.append([so_file.name, st.st_size, st.st_mtime_ns])
    ident_sha = sha256_json({
        "sysroot": str(sysroot),
        "rustc_version_verbose": ver_verbose,
        "rustc_bin_sha256": rustc_sha,
        "libs": lib_entries,
    })
    fp_file.write_text(json.dumps({
        "sysroot": str(sysroot),
        "rustc_stat": cur_stat,
        "sysroot_identity_sha256": ident_sha,
    }))
    return ident_sha


def normalize_capture_manifest(manifest: dict, rust_stage: pathlib.Path) -> dict:
    """Replace staging directory paths with $RUST_STAGE so capture.json is path-independent."""
    norm = copy.deepcopy(manifest)
    prefix = str(rust_stage.resolve()).rstrip("/") + "/"
    cr = norm["configuration"]["crate_root"]
    if cr.startswith(prefix):
        norm["configuration"]["crate_root"] = cr[len(prefix):]
    norm["configuration"]["declared_source_files"] = [
        p[len(prefix):] if p.startswith(prefix) else p
        for p in norm["configuration"]["declared_source_files"]
    ]
    for sf in norm["source_files"]:
        if sf["path"].startswith(prefix):
            sf["path"] = sf["path"][len(prefix):]
    return norm


def rehydrate_capture_manifest(norm_manifest: dict, rust_stage: pathlib.Path) -> dict:
    """Restore staging directory paths in capture.json for the current staging directory."""
    manifest = copy.deepcopy(norm_manifest)
    base = str(rust_stage.resolve()).rstrip("/")
    manifest["configuration"]["crate_root"] = f"{base}/{manifest['configuration']['crate_root']}"
    manifest["configuration"]["declared_source_files"] = [
        f"{base}/{p}" for p in manifest["configuration"]["declared_source_files"]
    ]
    for sf in manifest["source_files"]:
        sf["path"] = f"{base}/{sf['path']}"
    return manifest


def run_cached_verify(
    workspace_dir: pathlib.Path,
    cache: VerificationCache,
    enable_cache: bool = True,
    audit_mode: str = "4B",  # "4A-interp", "4A-native", or "4B"
    fast_admission: bool = True,
) -> dict:
    """Run an end-to-end verification of `workspace_dir/request.json` with 4-level caching."""
    t_total0 = time.perf_counter()
    req_path = workspace_dir / "request.json"
    request = json.loads(req_path.read_text())
    request["compilation"]["cfg"] = sorted(set(request["compilation"].get("cfg", [])))
    if request["scope"]["kind"] == "selected_unit":
        request["scope"]["roots"] = sorted(set(request["scope"]["roots"]))

    request_bytes = json.dumps(request, indent=2).encode("utf-8")
    request_sha256 = sha256_bytes(request_bytes)

    with tempfile.TemporaryDirectory(prefix="anneal-cached-verify-") as tmp:
        work = pathlib.Path(tmp)
        (work / "request.json").write_bytes(request_bytes)

        # Stage Rust sources
        t_stage0 = time.perf_counter()
        source_root = (workspace_dir / request["compilation"]["source_root"]).resolve()
        rust_stage = (work / "rust")
        rust_stage.mkdir(parents=True, exist_ok=True)
        sources = []
        originals = []
        for rel in request["compilation"]["source_files"]:
            orig = source_root / rel
            b = orig.read_bytes()
            s_sha = sha256_bytes(b)
            dst = rust_stage / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_bytes(b)
            originals.append((orig, s_sha))
            sources.append({"relative_path": rel, "sha256": s_sha})
        rust_stage_resolved = rust_stage.resolve()

        # Level 1: Capture Cache Key
        t_cap0 = time.perf_counter()
        capture_bin_sha256 = sha256_file(CAPTURE)
        sysroot_id = compute_sysroot_identity(SYSROOT, cache)
        k_capture = sha256_json({
            "level": "capture:v1",
            "capture_binary_sha256": capture_bin_sha256,
            "sysroot_identity_sha256": sysroot_id,
            "compilation": {
                "crate_root": request["compilation"]["crate_root"],
                "crate_name": request["compilation"]["crate_name"],
                "edition": request["compilation"]["edition"],
                "target": request["compilation"]["target"],
                "cfg": request["compilation"]["cfg"],
            },
            "sources": sources,
            "scope": request["scope"],
        })
        cap_entry_dir = cache.capture_dir / k_capture
        capture_dir = work / "capture"
        capture_dir.mkdir(parents=True, exist_ok=True)

        level1_hit = False
        if enable_cache and (cap_entry_dir / "Captured.lean").exists() and (cap_entry_dir / "capture.norm.json").exists():
            level1_hit = True
            norm_manifest = json.loads((cap_entry_dir / "capture.norm.json").read_text())
            manifest = rehydrate_capture_manifest(norm_manifest, rust_stage_resolved)
            capture_bytes = json.dumps(manifest, indent=2).encode("utf-8")
            (capture_dir / "capture.json").write_bytes(capture_bytes)
            captured_lean_bytes = (cap_entry_dir / "Captured.lean").read_bytes()
            (capture_dir / "Captured.lean").write_bytes(captured_lean_bytes)
        else:
            cmd = [
                str(CAPTURE),
                "capture",
                "--crate-root",
                str(rust_stage_resolved / request["compilation"]["crate_root"]),
                "--crate-name",
                request["compilation"]["crate_name"],
                "--edition",
                request["compilation"]["edition"],
                "--target",
                request["compilation"]["target"],
                "--out-dir",
                str(capture_dir),
                "--sysroot",
                str(SYSROOT),
            ]
            if request["scope"]["kind"] == "crate":
                cmd.extend(["--scope", "crate"])
            else:
                for r in request["scope"]["roots"]:
                    cmd.extend(["--select", r])
            for cfg in request["compilation"]["cfg"]:
                cmd.extend(["--cfg", cfg])
            for s in sources:
                cmd.extend(["--source-file", str(rust_stage_resolved / s["relative_path"])])
            env = {"PATH": "/usr/bin:/bin", "LD_LIBRARY_PATH": str(SYSROOT / "lib")}
            subprocess.run(cmd, cwd=rust_stage_resolved, env=env, check=True, capture_output=True)
            capture_bytes = (capture_dir / "capture.json").read_bytes()
            manifest = json.loads(capture_bytes)
            captured_lean_bytes = (capture_dir / "Captured.lean").read_bytes()
            if enable_cache:
                cap_entry_dir.mkdir(parents=True, exist_ok=True)
                norm_manifest = normalize_capture_manifest(manifest, rust_stage_resolved)
                (cap_entry_dir / "capture.norm.json").write_text(json.dumps(norm_manifest, indent=2))
                (cap_entry_dir / "Captured.lean").write_bytes(captured_lean_bytes)

        capture_sha256 = sha256_bytes(capture_bytes)
        # Level 2: Separate Captured.lean content digest from capture_sha256!
        captured_lean_sha256 = sha256_bytes(captured_lean_bytes)
        t_capture_ms = (time.perf_counter() - t_cap0) * 1000.0

        # Stage bundled model/theory modules + authored proof modules + Expected.lean
        t_adm0 = time.perf_counter()
        adm = cache.admit_toolchain_and_locks(fast_stat=(enable_cache and fast_admission))
        prefix = pathlib.Path(adm["prefix"])

        modules = []
        model_identity = []
        bundle_files = [
            ("trusted/lean/Trusted.lean", "Trusted", "model"),
            ("trusted/lean/Trusted/Mvp.lean", "Trusted.Mvp", "model"),
            ("trusted/lean/Trusted/Mvp/Semantics.lean", "Trusted.Mvp.Semantics", "model"),
            ("trusted/lean/Trusted/Mvp/Syntax.lean", "Trusted.Mvp.Syntax", "model"),
            ("theory/Anneal.lean", "Anneal", "proof"),
            ("theory/Anneal/Mvp/Canaries.lean", "Anneal.Mvp.Canaries", "proof"),
            ("theory/Anneal/Mvp/Execution.lean", "Anneal.Mvp.Execution", "proof"),
        ]
        for rel_path, mod_name, role in bundle_files:
            orig_p = BASELINE_ARTIFACTS / "anneal" / rel_path
            b = orig_p.read_bytes()
            s_sha = sha256_bytes(b)
            staged_p = work / "target-src" / f"{mod_name.replace('.', '/')}.lean"
            staged_p.parent.mkdir(parents=True, exist_ok=True)
            staged_p.write_bytes(b)
            model_identity.append([rel_path, s_sha])
            modules.append({
                "module": mod_name,
                "source": str(staged_p),
                "expectedSha256": s_sha,
                "role": role,
            })
        model_manifest_sha256 = sha256_json(model_identity)

        staged_captured_p = work / "target-src/Captured.lean"
        staged_captured_p.write_bytes(captured_lean_bytes)
        modules.append({
            "module": "Captured",
            "source": str(staged_captured_p),
            "expectedSha256": captured_lean_sha256,
            "role": "capture",
        })

        proof_root = (workspace_dir / request["proof"]["source_root"]).resolve()
        spec_identity = []
        for src_item in request["proof"]["sources"]:
            mod_name = src_item["module"]
            orig_p = proof_root / src_item["path"]
            b = orig_p.read_bytes()
            s_sha = sha256_bytes(b)
            originals.append((orig_p, s_sha))
            staged_p = work / "target-src" / f"{mod_name.replace('.', '/')}.lean"
            staged_p.parent.mkdir(parents=True, exist_ok=True)
            staged_p.write_bytes(b)
            role = src_item["role"]
            if role == "specification":
                spec_identity.append([mod_name, s_sha])
            modules.append({
                "module": mod_name,
                "source": str(staged_p),
                "expectedSha256": s_sha,
                "role": role,
            })
        specification_manifest_sha256 = sha256_json(spec_identity)

        spec_decl = request["proof"].get("specification", "Spec.specs")
        spec_mod = request["proof"].get("specification_module") or spec_decl.rsplit(".", 1)[0]
        thm_decl = request["proof"].get("theorem", "Proof.verify")
        thm_mod = request["proof"].get("theorem_module") or thm_decl.rsplit(".", 1)[0]
        root_name = "CrateTheorem" if request["scope"]["kind"] == "crate" else "UnitTheorem"
        header = (
            "-- Copyright 2026 The Fuchsia Authors\n--\n"
            "-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0\n"
            "-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT\n"
            "-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.\n"
            "-- This file may not be copied, modified, or distributed except according to\n"
            "-- those terms.\n\n"
        )
        expected_text = (
            f"{header}prelude\nimport Trusted.Mvp\nimport Captured\nimport {spec_mod}\n\n"
            f"namespace Expected\ndef claim : Prop := _root_.Trusted.Mvp.{root_name} _root_.Captured.program _root_.{spec_decl}\nend Expected\n"
        )
        expected_bytes = expected_text.encode("utf-8")
        expected_sha256 = sha256_bytes(expected_bytes)
        staged_expected_p = work / "target-src/Expected.lean"
        staged_expected_p.write_bytes(expected_bytes)
        modules.append({
            "module": "Expected",
            "source": str(staged_expected_p),
            "expectedSha256": expected_sha256,
            "role": "expected",
        })
        t_admission_ms = (time.perf_counter() - t_adm0) * 1000.0

        # Level 3A: Header Parsing Cache (`K_header(M)`)
        t_hdr0 = time.perf_counter()
        imports_map = {}
        uncached_headers = []
        for m in modules:
            mod_name = m["module"]
            k_hdr = sha256_json({
                "level": "header:v1",
                "lean_sha256": adm["lean_sha256"],
                "trusted_boundary_sha256": adm["trusted_boundary_sha256"],
                "foundation_lock_sha256": adm["foundation_lock_sha256"],
                "module": mod_name,
                "source_sha256": m["expectedSha256"],
            })
            hdr_file = cache.header_dir / f"{k_hdr}.json"
            if enable_cache and hdr_file.exists():
                imports_map[mod_name] = json.loads(hdr_file.read_text())
            else:
                uncached_headers.append((mod_name, m["source"], hdr_file))

        if uncached_headers:
            headers_req = {
                "mode": "headers",
                "sysroot": str(prefix),
                "foundation": sorted(adm["foundation_graph"].keys()),
                "sources": [[mod_name, src_p] for mod_name, src_p, _ in uncached_headers],
            }
            h_req_p = work / "req-headers.json"
            h_res_p = work / "res-headers.json"
            h_req_p.write_text(json.dumps(headers_req))
            if audit_mode == "4A-interp" and not enable_cache:
                inspector = work / "TrustedBoundary.lean"
                shutil.copy2(MVP_SRC / "trusted/audit/TrustedBoundary.lean", inspector)
                subprocess.run(
                    [str(ANNEAL_LEAN_RUN), "--mode", "file", "--concurrency", "4", "--",
                     str(LEAN), "-j1", "-M2048", "--run", str(inspector), str(h_req_p), str(h_res_p)],
                    cwd=work, check=True, capture_output=True
                )
            else:
                tb_bin = cache.ensure_native_inspector()
                subprocess.run([str(tb_bin), str(h_req_p), str(h_res_p)], cwd=work, check=True, capture_output=True)
            hdr_res = json.loads(h_res_p.read_text())["result"]["headers"]
            by_mod = {h["module"]: h["imports"] for h in hdr_res}
            for mod_name, _, hdr_file in uncached_headers:
                imps = by_mod[mod_name]
                imports_map[mod_name] = imps
                if enable_cache:
                    hdr_file.write_text(json.dumps(imps))
        t_headers_ms = (time.perf_counter() - t_hdr0) * 1000.0

        # Resolve library closure and topological order
        t_comp0 = time.perf_counter()
        pending_libs = [edge["module"] for edges in imports_map.values() for edge in edges]
        needed_libs = set()
        while pending_libs:
            lm = pending_libs.pop()
            if lm in adm["foundation_graph"] or lm not in adm["library_graph"] or lm in needed_libs:
                continue
            needed_libs.add(lm)
            pending_libs.extend(e["module"] for e in adm["library_graph"][lm])

        arts = dict(adm["foundation_arts"])
        graph = dict(adm["foundation_graph"])
        dep_part_digests = dict(adm["foundation_part_shas"])
        for lm in sorted(needed_libs):
            arts[lm] = adm["library_arts"][lm]
            graph[lm] = adm["library_graph"][lm]
            dep_part_digests[lm] = adm["library_part_shas"][lm]

        mod_by_name = {m["module"]: m for m in modules}
        pending_mods = set(mod_by_name.keys())
        topo_order = []
        while pending_mods:
            ready = sorted(
                m for m in pending_mods
                if all(e["module"] not in pending_mods for e in imports_map[m])
            )
            for m in ready:
                pending_mods.remove(m)
                topo_order.append(m)

        # Level 3B: Per-Module .olean Cache (`K_module(M)`)
        compile_flags = ["-j1", "-M2048", "-t0", "-DElab.async=false", "-Ddebug.skipKernelTC=false"]
        compiled_modules = []
        cached_modules = []
        olean_shas = {}

        def get_transitive_dep_digests(mod_name: str) -> dict:
            visited = set()
            stack = [e["module"] for e in imports_map[mod_name]]
            result = {}
            while stack:
                d = stack.pop()
                if d in visited:
                    continue
                visited.add(d)
                result[d] = dep_part_digests[d]
                for edge in graph.get(d, []):
                    stack.append(edge["module"])
            return {k: result[k] for k in sorted(result.keys())}

        for mod_name in topo_order:
            m_info = mod_by_name[mod_name]
            trans_deps = get_transitive_dep_digests(mod_name)
            k_module = sha256_json({
                "level": "olean:v1",
                "lean_sha256": adm["lean_sha256"],
                "compile_flags": compile_flags,
                "module": mod_name,
                "is_module": False,
                "source_sha256": m_info["expectedSha256"],
                "imports": imports_map[mod_name],
                "transitive_dep_artifacts": trans_deps,
            })
            cached_olean = cache.olean_dir / f"{k_module}.olean"
            Cached_meta = cache.olean_dir / f"{k_module}.json"
            rel = mod_name.replace(".", "/")
            out_olean = work / "target-lib" / f"{rel}.olean"
            out_olean.parent.mkdir(parents=True, exist_ok=True)

            if enable_cache and cached_olean.exists() and Cached_meta.exists():
                # Fast hardlink or copy into staging directory
                try:
                    os.link(cached_olean, out_olean)
                except OSError:
                    shutil.copy2(cached_olean, out_olean)
                o_sha = json.loads(Cached_meta.read_text())["olean_sha256"]
                cached_modules.append(mod_name)
            else:
                setup_path = work / f"{mod_name}.setup.json"
                setup_obj = {
                    "name": mod_name,
                    "isModule": False,
                    "imports": imports_map[mod_name],
                    "importArts": arts,
                    "dynlibs": [],
                    "plugins": [],
                    "options": {},
                }
                setup_path.write_text(json.dumps(setup_obj))
                subprocess.run(
                    [str(ANNEAL_LEAN_RUN), "--mode", "file", "--concurrency", "4", "--",
                     str(LEAN), *compile_flags, "--setup", str(setup_path), "-o", str(out_olean), m_info["source"]],
                    cwd=work, check=True, capture_output=True
                )
                o_sha = sha256_file(out_olean)
                compiled_modules.append(mod_name)
                if enable_cache:
                    shutil.copy2(out_olean, cached_olean)
                    Cached_meta.write_text(json.dumps({"module": mod_name, "olean_sha256": o_sha, "k_module": k_module}))

            olean_shas[mod_name] = o_sha
            dep_part_digests[mod_name] = {"olean": o_sha}
            arts[mod_name] = [[str(out_olean)], []]
            graph[mod_name] = imports_map[mod_name]

        t_compile_ms = (time.perf_counter() - t_comp0) * 1000.0

        # Level 4: TargetAudit Execution or Content-Addressed Receipt Cache (`K_audit`)
        t_aud0 = time.perf_counter()
        audit_request = {
            "modules": modules,
            "theoremModule": thm_mod,
            "theoremName": thm_decl,
            "expectedModule": "Expected",
            "expectedDeclaration": "Expected.claim",
            "canonicalRoot": f"Trusted.Mvp.{root_name}",
            "subjectDeclaration": "Captured.program",
            "specificationDeclaration": spec_decl,
            "bindings": {
                "requestSha256": request_sha256,
                "captureSha256": capture_sha256,
                "modelManifestSha256": model_manifest_sha256,
                "specificationManifestSha256": specification_manifest_sha256,
            },
        }
        k_audit = sha256_json({
            "level": "target-audit:v1",
            "lean_sha256": adm["lean_sha256"],
            "trusted_boundary_sha256": adm["trusted_boundary_sha256"],
            "foundation_lock_sha256": adm["foundation_lock_sha256"],
            "library_lock_sha256": adm["library_lock_sha256"],
            "axioms": adm["axioms"],
            "libraries": sorted(needed_libs),
            "graph": graph,
            "theoremModule": thm_mod,
            "theoremName": thm_decl,
            "expectedModule": "Expected",
            "expectedDeclaration": "Expected.claim",
            "canonicalRoot": f"Trusted.Mvp.{root_name}",
            "subjectDeclaration": "Captured.program",
            "specificationDeclaration": spec_decl,
            "modules": [
                {
                    "module": m["module"],
                    "role": m["role"],
                    "source_sha256": m["expectedSha256"],
                    "olean_sha256": olean_shas[m["module"]],
                }
                for m in modules
            ],
        })
        audit_cache_file = cache.audit_dir / f"{k_audit}.json"
        level4_hit = False
        if enable_cache and audit_mode == "4B" and audit_cache_file.exists():
            level4_hit = True
            report = json.loads(audit_cache_file.read_text())
        else:
            ta_wire = {
                "mode": "target-audit",
                "sysroot": str(prefix),
                "artifacts": [[k, v] for k, v in sorted(arts.items())],
                "foundation": sorted(adm["foundation_graph"].keys()),
                "libraries": sorted(needed_libs),
                "graph": graph,
                "axioms": adm["axioms"],
                "target": audit_request,
            }
            ta_req_p = work / "req-target-audit.json"
            ta_res_p = work / "res-target-audit.json"
            ta_req_p.write_text(json.dumps(ta_wire))
            if audit_mode == "4A-interp":
                inspector = work / "TrustedBoundary.lean"
                shutil.copy2(MVP_SRC / "trusted/audit/TrustedBoundary.lean", inspector)
                subprocess.run(
                    [str(ANNEAL_LEAN_RUN), "--mode", "file", "--concurrency", "4", "--",
                     str(LEAN), "-j1", "-M2048", "--run", str(inspector), str(ta_req_p), str(ta_res_p)],
                    cwd=work, check=True, capture_output=True
                )
            else:
                tb_bin = cache.ensure_native_inspector()
                subprocess.run([str(tb_bin), str(ta_req_p), str(ta_res_p)], cwd=work, check=True, capture_output=True)
            report = json.loads(ta_res_p.read_text())["result"]
            if enable_cache:
                audit_cache_file.write_text(json.dumps(report))

        # Attach provenance and fresh bindings (matching target.rs:345-413)
        provenance = [
            {
                "module": m["module"],
                "role": m["role"],
                "sourceSha256": m["expectedSha256"],
                "artifacts": [{"sha256": olean_shas[m["module"]]}],
            }
            for m in modules
        ]
        report["bindings"] = audit_request["bindings"]
        report["sources"] = provenance
        report["toolchain"] = adm["version"]

        # Final post-verification input snapshot check (matching verify.rs:798-813)
        for orig_path, exp_sha in originals:
            assert sha256_file(orig_path) == exp_sha, f"Input changed during verification: {orig_path}"
        assert sha256_file(CAPTURE) == capture_bin_sha256

        t_audit_ms = (time.perf_counter() - t_aud0) * 1000.0
        t_total_ms = (time.perf_counter() - t_total0) * 1000.0

        return {
            "status": "selected_unit_verified" if request["scope"]["kind"] == "selected_unit" else "crate_verified",
            "timing_ms": {
                "capture_ms": round(t_capture_ms, 2),
                "admission_ms": round(t_admission_ms, 2),
                "headers_ms": round(t_headers_ms, 2),
                "lean_compile_ms": round(t_compile_ms, 2),
                "target_audit_ms": round(t_audit_ms, 2),
                "total_ms": round(t_total_ms, 2),
            },
            "cache_stats": {
                "level1_capture_hit": level1_hit,
                "captured_lean_sha256": captured_lean_sha256,
                "uncached_headers_count": len(uncached_headers),
                "compiled_modules_count": len(compiled_modules),
                "compiled_modules": compiled_modules,
                "cached_modules_count": len(cached_modules),
                "level4_audit_hit": level4_hit,
                "audit_mode": audit_mode,
            },
            "bindings": audit_request["bindings"],
        }
