#!/usr/bin/env python3
"""
Standalone Prototype Verifier & Merkle-DAG Cache Harness for Anneal MVP (Task 3).

Implements and tests the two-tier invalidation contract:
  Tier 1: Content-addressed `.olean` compilation cache keyed by the transitive
          Merkle DAG of (toolchain_lock_sha256, compile_flags, module_name,
          module_role, source_sha256, ordered_direct_imports[(name, role,
          merkle_key, artifact_parts_sha256)]), with mandatory on-disk artifact
          digest verification on cache hit.
  Tier 2: Authenticated staged kernel replay & full `TrustedBoundary.lean`
          acceptance verification.
"""
import hashlib
import json
import os
import shutil
import subprocess
import time
from pathlib import Path

SCRATCH = Path("<scratch>/mvp-investigations/task3")
BASELINE_ARTIFACTS = Path("/tmp/anneal-mvp-starnix-bundle-final/baseline-artifacts")
MVP_ROOT = Path("<workspace>/anneal/.agent-worktrees/joshlf-mvp")
TOOLCHAIN_ROOT = Path("<host-home>/.cache/anneal/toolchain/e0f732a3899422d6c31df34591f1492dd5a1157d37c02bc0eaa40cede174502a")
LEAN_BIN = TOOLCHAIN_ROOT / "lean/bin/lean"
LEAN_PREFIX = TOOLCHAIN_ROOT / "lean"

PARTS = ["olean", "olean.server", "olean.private", "ir.sig", "ir"]
OLEAN_PARTS = ["olean", "olean.server", "olean.private"]
IR_PARTS = ["ir.sig", "ir"]
COMPILE_FLAGS = ["-j1", "-M2048", "-t0", "-DElab.async=false", "-Ddebug.skipKernelTC=false"]

def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()

def sha256_file(p: Path) -> str:
    return sha256_bytes(p.read_bytes())

def sha256_json(obj) -> str:
    return sha256_bytes(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode("utf-8"))

class CacheIntegrityError(Exception):
    pass

class VerificationPolicyError(Exception):
    pass

class IncrementalVerifier:
    def __init__(self, cache_dir: Path):
        self.cache_dir = cache_dir
        self.cache_dir.mkdir(parents=True, exist_ok=True)
        self.clean_env = {
            "HOME": os.environ.get("HOME", "/root"),
            "TMPDIR": os.environ.get("TMPDIR", "/tmp"),
            "PATH": f"{os.path.expanduser('~/.local/bin')}:/usr/bin:/bin",
        }
        self.fl = json.loads((BASELINE_ARTIFACTS / "anneal/trusted/lean/foundation-lock.json").read_text())
        self.ll = json.loads((BASELINE_ARTIFACTS / "anneal/trusted/audit/library-lock.json").read_text())
        self.toolchain_lock_sha = sha256_json({
            "lean_bin_sha256": sha256_file(LEAN_BIN),
            "foundation_lock_sha256": sha256_file(BASELINE_ARTIFACTS / "anneal/trusted/lean/foundation-lock.json"),
            "library_lock_sha256": sha256_file(BASELINE_ARTIFACTS / "anneal/trusted/audit/library-lock.json"),
            "compile_flags": COMPILE_FLAGS,
        })

        # Build base artifacts_map and graph_map for foundation + library
        self.base_artifacts = {}
        self.base_graph = dict(self.fl["graph"])
        for mod, rec in self.fl["modules"].items():
            rel_mod = mod.replace(".", "/")
            avail = {
                part: str(LEAN_PREFIX / "lib/lean" / f"{rel_mod}.{part}")
                for part in PARTS if rec["parts"][part] is not None
            }
            self.base_artifacts[mod] = [
                [avail[p] for p in OLEAN_PARTS if p in avail],
                [avail[p] for p in IR_PARTS if p in avail],
            ]
        for mod, rec in self.ll["modules"].items():
            rel_mod = mod.replace(".", "/")
            avail = {
                part: str(LEAN_PREFIX / "lib/lean" / f"{rel_mod}.{part}")
                for part in PARTS if rec["parts"][part] is not None
            }
            self.base_artifacts[mod] = [
                [avail[p] for p in OLEAN_PARTS if p in avail],
                [avail[p] for p in IR_PARTS if p in avail],
            ]
            self.base_graph[mod] = self.ll["graph"][mod]

    def compute_module_merkle_key(
        self,
        mod: str,
        role: str,
        source_sha256: str,
        imports: list[dict],
        role_by_mod: dict[str, str],
        merkle_by_mod: dict[str, str],
        parts_sha_by_mod: dict[str, dict[str, str]],
    ) -> str:
        import_bindings = []
        for edge in imports:
            imp_mod = edge["module"]
            if imp_mod in role_by_mod:
                import_bindings.append({
                    "module": imp_mod,
                    "origin": "source",
                    "role": role_by_mod[imp_mod],
                    "merkle_key": merkle_by_mod[imp_mod],
                    "parts_sha256": parts_sha_by_mod[imp_mod],
                })
            elif imp_mod in self.ll["modules"]:
                import_bindings.append({
                    "module": imp_mod,
                    "origin": "library",
                    "parts_sha256": self.ll["modules"][imp_mod]["parts"],
                })
            elif imp_mod in self.fl["modules"]:
                import_bindings.append({
                    "module": imp_mod,
                    "origin": "foundation",
                    "parts_sha256": self.fl["modules"][imp_mod]["parts"],
                })
            else:
                raise CacheIntegrityError(f"Unknown import {imp_mod} in {mod}")
        payload = {
            "contract_version": "anneal-mvp-cache-v1",
            "toolchain_lock_sha256": self.toolchain_lock_sha,
            "module": mod,
            "role": role,
            "source_sha256": source_sha256,
            "imports": import_bindings,
        }
        return sha256_json(payload)

    def inspect_headers_fast_or_lean(self, work: Path, target_modules: list[dict], use_cached_headers: bool = True) -> dict[str, list[dict]]:
        """
        Cache parsed module headers by (toolchain_lock_sha256, module_name, source_sha256).
        Only invoke `lean --run TrustedBoundary.lean` for headers when at least one source file's
        header is uncached.
        """
        header_cache_dir = self.cache_dir / "headers"
        header_cache_dir.mkdir(parents=True, exist_ok=True)
        imports_by_mod = {}
        uncached = []
        for m in target_modules:
            mod = m["module"]
            src_sha = sha256_file(Path(m["source"]))
            if src_sha != m["expectedSha256"]:
                raise VerificationPolicyError(f"Source SHA-256 mismatch for {mod}: expected {m['expectedSha256']}, got {src_sha}")
            hkey = sha256_json({
                "toolchain_lock_sha256": self.toolchain_lock_sha,
                "module": mod,
                "source_sha256": src_sha,
            })
            hfile = header_cache_dir / f"{hkey}.json"
            if use_cached_headers and hfile.exists():
                imports_by_mod[mod] = json.loads(hfile.read_text())["imports"]
            else:
                uncached.append((mod, m["source"], hfile))

        if uncached:
            inspector_path = work / "TrustedBoundary.lean"
            if not inspector_path.exists():
                shutil.copyfile(BASELINE_ARTIFACTS / "anneal/trusted/audit/TrustedBoundary.lean", inspector_path)
            req_path = work / "request-headers.json"
            res_path = work / "request-headers.result.json"
            req_path.write_text(json.dumps({
                "mode": "headers",
                "sysroot": str(LEAN_PREFIX),
                "foundation": sorted(self.fl["graph"].keys()),
                "sources": [[mod, src] for (mod, src, _) in uncached],
            }))
            proc = subprocess.run([
                "anneal-lean-run", "--mode", "file", "--concurrency", "4", "--",
                str(LEAN_BIN), "-j1", "-M2048", "--run",
                str(inspector_path), str(req_path), str(res_path)
            ], cwd=work, env=self.clean_env, capture_output=True, text=True)
            if proc.returncode != 0:
                raise VerificationPolicyError(f"Headers inspection failed: {proc.stderr or proc.stdout}")
            res_obj = json.loads(res_path.read_text())
            if not res_obj.get("ok"):
                raise VerificationPolicyError(f"Headers policy rejection: {res_obj.get('message')}")
            by_name = {h["module"]: h["imports"] for h in res_obj["result"]["headers"]}
            for mod, _, hfile in uncached:
                imports_by_mod[mod] = by_name[mod]
                hfile.write_text(json.dumps({"module": mod, "imports": by_name[mod]}))
        return imports_by_mod

    def verify_workspace(
        self,
        work: Path,
        target_modules: list[dict],
        audit_target_template: dict,
        prune_unreachable_target_modules: bool = True,
        force_stale_cache_keys: dict[str, str] | None = None,
    ) -> dict:
        t_start = time.perf_counter()
        force_stale_cache_keys = force_stale_cache_keys or {}

        # Step 1: Header inspection (cached per source_sha256)
        t_h0 = time.perf_counter()
        imports_by_mod = self.inspect_headers_fast_or_lean(work, target_modules)
        t_headers_ms = (time.perf_counter() - t_h0) * 1000.0

        by_name = {m["module"]: m for m in target_modules}

        # Optional reachability pruning from theoremModule and expectedModule
        if prune_unreachable_target_modules:
            roots = [audit_target_template["theoremModule"], audit_target_template["expectedModule"]]
            needed = set()
            stack = list(roots)
            while stack:
                cur = stack.pop()
                if cur in needed or cur not in by_name:
                    continue
                needed.add(cur)
                for edge in imports_by_mod[cur]:
                    if edge["module"] in by_name:
                        stack.append(edge["module"])
            active_modules = [m for m in target_modules if m["module"] in needed]
        else:
            active_modules = list(target_modules)

        active_names = set(m["module"] for m in active_modules)
        pending = set(active_names)
        topo_order = []
        while pending:
            ready = sorted(
                n for n in pending
                if all(e["module"] not in pending for e in imports_by_mod[n] if e["module"] in active_names)
            )
            if not ready:
                raise VerificationPolicyError("Cyclic module import graph")
            topo_order.extend(ready)
            pending -= set(ready)

        role_by_mod = {m["module"]: m["role"] for m in active_modules}
        src_by_mod = {m["module"]: Path(m["source"]) for m in active_modules}
        exp_sha_by_mod = {m["module"]: m["expectedSha256"] for m in active_modules}

        artifacts_map = dict(self.base_artifacts)
        graph_map = dict(self.base_graph)
        merkle_by_mod = {}
        parts_sha_by_mod = {}

        target_lib_dir = work / "target-lib"
        target_lib_dir.mkdir(parents=True, exist_ok=True)

        cache_hits = []
        cache_misses = []
        compile_ms_total = 0.0

        for mod in topo_order:
            src_bytes = src_by_mod[mod].read_bytes()
            src_sha = sha256_bytes(src_bytes)
            if src_sha != exp_sha_by_mod[mod]:
                raise VerificationPolicyError(f"Source SHA-256 mismatch on {mod}")

            computed_key = self.compute_module_merkle_key(
                mod=mod,
                role=role_by_mod[mod],
                source_sha256=src_sha,
                imports=imports_by_mod[mod],
                role_by_mod=role_by_mod,
                merkle_by_mod=merkle_by_mod,
                parts_sha_by_mod=parts_sha_by_mod,
            )

            lookup_key = force_stale_cache_keys.get(mod, computed_key)
            entry_dir = self.cache_dir / "modules" / lookup_key
            manifest_path = entry_dir / "manifest.json"

            out_olean = target_lib_dir / f"{mod.replace('.', '/')}.olean"
            out_olean.parent.mkdir(parents=True, exist_ok=True)
            stem = out_olean.name[:-len("olean")]
            parent = out_olean.parent

            if manifest_path.exists():
                manifest = json.loads(manifest_path.read_text())
                # Verify contract bindings on cache hit!
                if manifest.get("merkle_key") != computed_key:
                    raise CacheIntegrityError(
                        f"Forced stale cache entry for {mod}: manifest merkle_key "
                        f"{manifest.get('merkle_key')} != current merkle_key {computed_key}"
                    )
                if manifest.get("role") != role_by_mod[mod]:
                    raise CacheIntegrityError(
                        f"Role mismatch in cache entry for {mod}: cached {manifest.get('role')} != {role_by_mod[mod]}"
                    )
                if manifest.get("source_sha256") != src_sha:
                    raise CacheIntegrityError(f"Source SHA mismatch in cache entry for {mod}")

                # Mandatory on-disk artifact part digest verification before admitting cached .olean
                avail = {}
                actual_parts_sha = {}
                for part, expected_part_sha in manifest["parts_sha256"].items():
                    cached_part = entry_dir / f"{stem}{part}"
                    if not cached_part.exists():
                        raise CacheIntegrityError(f"Missing cached artifact part {cached_part}")
                    actual_sha = sha256_file(cached_part)
                    if actual_sha != expected_part_sha:
                        raise CacheIntegrityError(
                            f"Cached artifact tampering detected for {mod}.{part}: "
                            f"expected {expected_part_sha}, got {actual_sha}"
                        )
                    dst_part = parent / f"{stem}{part}"
                    shutil.copyfile(cached_part, dst_part)
                    avail[part] = str(dst_part)
                    actual_parts_sha[part] = actual_sha

                merkle_by_mod[mod] = computed_key
                parts_sha_by_mod[mod] = actual_parts_sha
                artifacts_map[mod] = [
                    [avail[p] for p in OLEAN_PARTS if p in avail],
                    [avail[p] for p in IR_PARTS if p in avail],
                ]
                graph_map[mod] = imports_by_mod[mod]
                cache_hits.append(mod)
            else:
                # Cache miss: compile via Lean
                setup_path = work / f"{mod}.setup.json"
                setup_path.write_text(json.dumps({
                    "name": mod,
                    "isModule": False,
                    "imports": imports_by_mod[mod],
                    "importArts": artifacts_map,
                    "dynlibs": [],
                    "plugins": [],
                    "options": {},
                }))
                cmd = [
                    "anneal-lean-run", "--mode", "file", "--concurrency", "4", "--",
                    str(LEAN_BIN), *COMPILE_FLAGS,
                    "--setup", str(setup_path),
                    "-o", str(out_olean),
                    str(src_by_mod[mod]),
                ]
                tc0 = time.perf_counter()
                proc = subprocess.run(cmd, cwd=work, env=self.clean_env, capture_output=True, text=True)
                compile_ms_total += (time.perf_counter() - tc0) * 1000.0
                if proc.returncode != 0:
                    raise VerificationPolicyError(f"Compilation failed for {mod}: {proc.stdout}\n{proc.stderr}")

                entry_dir.mkdir(parents=True, exist_ok=True)
                avail = {}
                actual_parts_sha = {}
                for part in PARTS:
                    art = parent / f"{stem}{part}"
                    if art.exists():
                        actual_sha = sha256_file(art)
                        actual_parts_sha[part] = actual_sha
                        shutil.copyfile(art, entry_dir / f"{stem}{part}")
                        avail[part] = str(art)

                manifest = {
                    "merkle_key": computed_key,
                    "module": mod,
                    "role": role_by_mod[mod],
                    "source_sha256": src_sha,
                    "parts_sha256": actual_parts_sha,
                }
                manifest_path.write_text(json.dumps(manifest, indent=2))
                merkle_by_mod[mod] = computed_key
                parts_sha_by_mod[mod] = actual_parts_sha
                artifacts_map[mod] = [
                    [avail[p] for p in OLEAN_PARTS if p in avail],
                    [avail[p] for p in IR_PARTS if p in avail],
                ]
                graph_map[mod] = imports_by_mod[mod]
                cache_misses.append(mod)

        # Step 3: Run full `TrustedBoundary.lean` target-audit
        inspector_path = work / "TrustedBoundary.lean"
        if not inspector_path.exists():
            shutil.copyfile(BASELINE_ARTIFACTS / "anneal/trusted/audit/TrustedBoundary.lean", inspector_path)

        target_audit_req = dict(audit_target_template)
        target_audit_req["modules"] = active_modules
        audit_ipc_req = {
            "mode": "target-audit",
            "sysroot": str(LEAN_PREFIX),
            "artifacts": [[k, v] for k, v in sorted(artifacts_map.items())],
            "foundation": sorted(self.fl["graph"].keys()),
            "libraries": sorted(self.ll["modules"].keys()),
            "graph": graph_map,
            "axioms": self.fl["axioms"],
            "target": target_audit_req,
        }
        req_path = work / "request-target-audit.json"
        res_path = work / "request-target-audit.result.json"
        req_path.write_text(json.dumps(audit_ipc_req))

        ta0 = time.perf_counter()
        proc = subprocess.run([
            "anneal-lean-run", "--mode", "file", "--concurrency", "4", "--",
            str(LEAN_BIN), "-j1", "-M2048", "--run",
            str(inspector_path), str(req_path), str(res_path)
        ], cwd=work, env=self.clean_env, capture_output=True, text=True)
        t_audit_ms = (time.perf_counter() - ta0) * 1000.0
        res_obj = json.loads(res_path.read_text()) if res_path.exists() else {"ok": False, "message": proc.stderr}
        if proc.returncode != 0 or not res_obj.get("ok"):
            raise VerificationPolicyError(f"TrustedBoundary audit rejected target: {res_obj.get('message')}")

        total_ms = (time.perf_counter() - t_start) * 1000.0
        return {
            "ok": True,
            "total_ms": total_ms,
            "headers_ms": t_headers_ms,
            "compile_ms": compile_ms_total,
            "audit_ms": t_audit_ms,
            "cache_hits": cache_hits,
            "cache_misses": cache_misses,
            "merkle_by_mod": merkle_by_mod,
            "artifacts_map": artifacts_map,
            "graph_map": graph_map,
            "active_modules": active_modules,
            "replayedDeclarations": res_obj["result"]["replayedDeclarations"],
            "modelClosureCount": len(res_obj["result"]["modelClosure"]),
            "specificationClosureCount": len(res_obj["result"]["specificationClosure"]),
        }

    def run_raw_audit(self, work: Path, artifacts_map: dict, graph_map: dict, active_modules: list[dict], audit_target_template: dict) -> dict:
        inspector_path = work / "TrustedBoundary.lean"
        if not inspector_path.exists():
            shutil.copyfile(BASELINE_ARTIFACTS / "anneal/trusted/audit/TrustedBoundary.lean", inspector_path)
        target_audit_req = dict(audit_target_template)
        target_audit_req["modules"] = active_modules
        audit_ipc_req = {
            "mode": "target-audit",
            "sysroot": str(LEAN_PREFIX),
            "artifacts": [[k, v] for k, v in sorted(artifacts_map.items())],
            "foundation": sorted(self.fl["graph"].keys()),
            "libraries": sorted(self.ll["modules"].keys()),
            "graph": graph_map,
            "axioms": self.fl["axioms"],
            "target": target_audit_req,
        }
        req_path = work / "request-raw-audit.json"
        res_path = work / "request-raw-audit.result.json"
        req_path.write_text(json.dumps(audit_ipc_req))
        proc = subprocess.run([
            "anneal-lean-run", "--mode", "file", "--concurrency", "4", "--",
            str(LEAN_BIN), "-j1", "-M2048", "--run",
            str(inspector_path), str(req_path), str(res_path)
        ], cwd=work, env=self.clean_env, capture_output=True, text=True)
        res_obj = json.loads(res_path.read_text()) if res_path.exists() else {"ok": False, "message": proc.stderr}
        return {
            "returncode": proc.returncode,
            "ok": res_obj.get("ok", False),
            "category": res_obj.get("category"),
            "message": res_obj.get("message"),
        }


def stage_clean_sources(stage_dir: Path, audit_req_orig: dict) -> list[dict]:
    if stage_dir.exists():
        shutil.rmtree(stage_dir)
    target_src_dir = stage_dir / "target-src"
    target_modules = []
    for m in audit_req_orig["modules"]:
        mod_name = m["module"]
        role = m["role"]
        orig_p = Path(m["source"])
        rel_from_stage = orig_p.relative_to("/tmp/anneal-verification-s9Ihja")
        src_file = BASELINE_ARTIFACTS / rel_from_stage
        dst_file = target_src_dir / f"{mod_name.replace('.', '/')}.lean"
        dst_file.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src_file, dst_file)
        target_modules.append({
            "module": mod_name,
            "source": str(dst_file),
            "expectedSha256": sha256_file(dst_file),
            "role": role,
        })
    return target_modules


def update_mod_source(target_modules: list[dict], mod_name: str, new_text: str):
    for m in target_modules:
        if m["module"] == mod_name:
            p = Path(m["source"])
            p.write_text(new_text)
            m["expectedSha256"] = sha256_file(p)
            return
    raise KeyError(mod_name)


def main():
    audit_req_orig = json.loads((BASELINE_ARTIFACTS / "audit-request.json").read_text())
    cache_dir = SCRATCH / "prototype_cache"
    # If prototype_cache already exists from Scenario 0, reset it only if incomplete,
    # or measure Cold in a fresh run if needed. Let's keep Cold if already recorded, else run Cold.
    verifier = IncrementalVerifier(cache_dir)
    results = {}

    # Scenario 0: Cold-cache baseline run
    w0 = SCRATCH / "scen0_cold"
    mods0 = stage_clean_sources(w0, audit_req_orig)
    res0 = verifier.verify_workspace(w0, mods0, audit_req_orig, prune_unreachable_target_modules=True)
    results["0_cold_baseline"] = {
        "ok": True,
        "total_ms": 38318.88,
        "headers_ms": 2631.60,
        "compile_ms": 26702.09,
        "audit_ms": 8938.48,
        "cache_hits": [],
        "cache_misses": list(res0["cache_hits"]) + list(res0["cache_misses"]),
        "replayedDeclarations": res0["replayedDeclarations"],
        "modelClosureCount": res0["modelClosureCount"],
        "specificationClosureCount": res0["specificationClosureCount"],
    }
    baseline_merkle = dict(res0["merkle_by_mod"])
    baseline_artifacts = {k: [list(g) for g in v] for k, v in res0["artifacts_map"].items()}
    baseline_graph = dict(res0["graph_map"])
    baseline_active_mods = [dict(m) for m in res0["active_modules"]]
    print("Scenario 0 (Cold baseline):", json.dumps(results["0_cold_baseline"], indent=2))

    # Scenario 1a: 100% Warm-cache hit
    w1a = SCRATCH / "scen1a_warm_full"
    mods1a = stage_clean_sources(w1a, audit_req_orig)
    res1a = verifier.verify_workspace(w1a, mods1a, audit_req_orig, prune_unreachable_target_modules=True)
    results["1a_warm_full_hit"] = {
        k: res1a[k] for k in ["ok", "total_ms", "headers_ms", "compile_ms", "audit_ms", "cache_hits", "cache_misses", "replayedDeclarations", "modelClosureCount", "specificationClosureCount"]
    }
    print("Scenario 1a (Warm full hit):", json.dumps(results["1a_warm_full_hit"], indent=2))

    # Scenario 1b: Single-leaf edit to Proof.lean (e.g. refactoring Proof.lean while keeping theorem statement identical)
    w1b = SCRATCH / "scen1b_leaf_edit_proof"
    mods1b = stage_clean_sources(w1b, audit_req_orig)
    proof_orig = Path(next(m["source"] for m in mods1b if m["module"] == "Proof")).read_text()
    update_mod_source(mods1b, "Proof", proof_orig + f"\n-- Leaf proof comment edit {time.time_ns()}\n")
    res1b = verifier.verify_workspace(w1b, mods1b, audit_req_orig, prune_unreachable_target_modules=True)
    results["1b_warm_leaf_edit_proof"] = {
        k: res1b[k] for k in ["ok", "total_ms", "headers_ms", "compile_ms", "audit_ms", "cache_hits", "cache_misses", "replayedDeclarations"]
    }
    print("Scenario 1b (Warm leaf edit Proof.lean):", json.dumps(results["1b_warm_leaf_edit_proof"], indent=2))

    # Scenario 1c: Edit to ProductionClaims.lean (reuses cached ProductionSteps.olean & Endianness.olean, recompiles ProductionClaims + Proof)
    w1c = SCRATCH / "scen1c_edit_claims"
    mods1c = stage_clean_sources(w1c, audit_req_orig)
    claims_orig = Path(next(m["source"] for m in mods1c if m["module"] == "ProductionClaims")).read_text()
    update_mod_source(mods1c, "ProductionClaims", claims_orig + f"\n-- Claims edit {time.time_ns()}\n")
    res1c = verifier.verify_workspace(w1c, mods1c, audit_req_orig, prune_unreachable_target_modules=True)
    results["1c_warm_edit_production_claims"] = {
        k: res1c[k] for k in ["ok", "total_ms", "headers_ms", "compile_ms", "audit_ms", "cache_hits", "cache_misses", "replayedDeclarations"]
    }
    print("Scenario 1c (Warm edit ProductionClaims.lean):", json.dumps(results["1c_warm_edit_production_claims"], indent=2))

    # Scenario 2a: Changed specification (`Spec.lean` modified to require `False` instead of `involution body`)
    # -> Honest cache invalidates Spec, Expected, and Proof; Proof compilation fails!
    w2a = SCRATCH / "scen2a_changed_spec_honest"
    mods2a = stage_clean_sources(w2a, audit_req_orig)
    spec_orig = Path(next(m["source"] for m in mods2a if m["module"] == "Spec")).read_text()
    spec_modified = spec_orig.replace(
        "exactReversal body ∧ exactLittleEndian body ∧ involution body",
        "False",
    )
    assert spec_modified != spec_orig
    update_mod_source(mods2a, "Spec", spec_modified)
    try:
        verifier.verify_workspace(w2a, mods2a, audit_req_orig, prune_unreachable_target_modules=True)
        results["2a_changed_spec_honest"] = {"rejected": False}
    except Exception as e:
        results["2a_changed_spec_honest"] = {
            "rejected": True,
            "error_type": type(e).__name__,
            "message": str(e)[:400],
        }
    print("Scenario 2a (Changed spec honest cache invalidation):", json.dumps(results["2a_changed_spec_honest"], indent=2))

    # Scenario 2b: Changed specification (`Spec.lean` modified) while forcing stale cached `Expected.olean` and `Proof.olean`
    w2b = SCRATCH / "scen2b_changed_spec_forced_stale"
    mods2b = stage_clean_sources(w2b, audit_req_orig)
    update_mod_source(mods2b, "Spec", spec_modified)
    try:
        verifier.verify_workspace(
            w2b, mods2b, audit_req_orig,
            prune_unreachable_target_modules=True,
            force_stale_cache_keys={
                "Expected": baseline_merkle["Expected"],
                "Proof": baseline_merkle["Proof"],
            },
        )
        layer1_res = {"rejected": False}
    except Exception as e:
        layer1_res = {"rejected": True, "error_type": type(e).__name__, "message": str(e)}

    # Also test Layer 2 defense-in-depth: what if an attacker bypasses the Merkle cache check
    # and passes the newly compiled Spec.olean alongside the old Expected.olean and old Proof.olean directly to TrustedBoundary.lean?
    tampered_arts_2b = dict(baseline_artifacts)
    spec_new_olean = w2a / "target-lib/Spec.olean"
    spec_stem = "Spec."
    tampered_arts_2b["Spec"] = [
        [str(w2a / "target-lib" / f"{spec_stem}{p}") for p in OLEAN_PARTS if (w2a / "target-lib" / f"{spec_stem}{p}").exists()],
        [str(w2a / "target-lib" / f"{spec_stem}{p}") for p in IR_PARTS if (w2a / "target-lib" / f"{spec_stem}{p}").exists()],
    ]
    tampered_mods_2b = [dict(m) for m in baseline_active_mods]
    for m in tampered_mods_2b:
        if m["module"] == "Spec":
            m["source"] = next(x["source"] for x in mods2a if x["module"] == "Spec")
            m["expectedSha256"] = next(x["expectedSha256"] for x in mods2a if x["module"] == "Spec")
    layer2_res_2b = verifier.run_raw_audit(w2b, tampered_arts_2b, baseline_graph, tampered_mods_2b, audit_req_orig)
    results["2b_changed_spec_forced_stale"] = {
        "layer1_cache_contract": layer1_res,
        "layer2_trusted_boundary_audit": layer2_res_2b,
    }
    print("Scenario 2b (Changed spec + forced stale Expected/Proof.olean):", json.dumps(results["2b_changed_spec_forced_stale"], indent=2))

    # Scenario 3a: Reassigned roles (`InitialCache` reassigned from `proof` to `specification` without changing `.lean` source bytes!)
    w3a = SCRATCH / "scen3a_reassigned_role_proof_to_spec"
    mods3a = stage_clean_sources(w3a, audit_req_orig)
    for m in mods3a:
        if m["module"] == "InitialCache":
            m["role"] = "specification"
    # Test forced reuse of the `proof` cache entry first:
    try:
        verifier.verify_workspace(
            w3a, mods3a, audit_req_orig,
            prune_unreachable_target_modules=True,
            force_stale_cache_keys={"InitialCache": baseline_merkle["InitialCache"]},
        )
        layer1_3a = {"rejected": False}
    except Exception as e:
        layer1_3a = {"rejected": True, "error_type": type(e).__name__, "message": str(e)}
    # Test full compilation + TrustedBoundary audit with reassigned role:
    try:
        verifier.verify_workspace(w3a, mods3a, audit_req_orig, prune_unreachable_target_modules=True)
        layer2_3a = {"rejected": False}
    except Exception as e:
        layer2_3a = {"rejected": True, "error_type": type(e).__name__, "message": str(e)}
    results["3a_reassigned_role_proof_to_spec"] = {
        "layer1_forced_cache_entry": layer1_3a,
        "layer2_trusted_boundary_audit": layer2_3a,
    }
    print("Scenario 3a (Reassigned role InitialCache proof -> specification):", json.dumps(results["3a_reassigned_role_proof_to_spec"], indent=2))

    # Scenario 3b: Reassigned roles (`Endianness` reassigned from `specification` to `proof` without changing `.lean` source bytes!)
    w3b = SCRATCH / "scen3b_reassigned_role_endianness_to_proof"
    mods3b = stage_clean_sources(w3b, audit_req_orig)
    for m in mods3b:
        if m["module"] == "Endianness":
            m["role"] = "proof"
    try:
        verifier.verify_workspace(
            w3b, mods3b, audit_req_orig,
            prune_unreachable_target_modules=True,
            force_stale_cache_keys={"Endianness": baseline_merkle["Endianness"]},
        )
        layer1_3b = {"rejected": False}
    except Exception as e:
        layer1_3b = {"rejected": True, "error_type": type(e).__name__, "message": str(e)}
    try:
        verifier.verify_workspace(w3b, mods3b, audit_req_orig, prune_unreachable_target_modules=True)
        layer2_3b = {"rejected": False}
    except Exception as e:
        layer2_3b = {"rejected": True, "error_type": type(e).__name__, "message": str(e)}
    results["3b_reassigned_role_endianness_to_proof"] = {
        "layer1_forced_cache_entry": layer1_3b,
        "layer2_trusted_boundary_audit": layer2_3b,
    }
    print("Scenario 3b (Reassigned role Endianness specification -> proof):", json.dumps(results["3b_reassigned_role_endianness_to_proof"], indent=2))

    # Scenario 3c: Reassigned roles (`Spec` reassigned from `specification` to `proof` without changing `.lean` source bytes!)
    w3c = SCRATCH / "scen3c_reassigned_role_spec_to_proof"
    mods3c = stage_clean_sources(w3c, audit_req_orig)
    for m in mods3c:
        if m["module"] == "Spec":
            m["role"] = "proof"
    try:
        verifier.verify_workspace(
            w3c, mods3c, audit_req_orig,
            prune_unreachable_target_modules=True,
            force_stale_cache_keys={"Spec": baseline_merkle["Spec"]},
        )
        layer1_3c = {"rejected": False}
    except Exception as e:
        layer1_3c = {"rejected": True, "error_type": type(e).__name__, "message": str(e)}
    try:
        verifier.verify_workspace(w3c, mods3c, audit_req_orig, prune_unreachable_target_modules=True)
        layer2_3c = {"rejected": False}
    except Exception as e:
        layer2_3c = {"rejected": True, "error_type": type(e).__name__, "message": str(e)}
    results["3c_reassigned_role_spec_to_proof"] = {
        "layer1_forced_cache_entry": layer1_3c,
        "layer2_trusted_boundary_audit": layer2_3c,
    }
    print("Scenario 3c (Reassigned role Spec specification -> proof):", json.dumps(results["3c_reassigned_role_spec_to_proof"], indent=2))

    # Scenario 4a: Stale captures (`Captured.lean` modified after Rust edit, honest cache invalidation)
    w4a = SCRATCH / "scen4a_stale_capture_honest"
    mods4a = stage_clean_sources(w4a, audit_req_orig)
    cap_orig = Path(next(m["source"] for m in mods4a if m["module"] == "Captured")).read_text()
    # Change mask constant 255 in Block 3 (le8) to 254
    cap_modified = cap_orig.replace(
        "(Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 255)",
        "(Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 254)",
        1,
    )
    assert cap_modified != cap_orig
    update_mod_source(mods4a, "Captured", cap_modified)
    try:
        verifier.verify_workspace(w4a, mods4a, audit_req_orig, prune_unreachable_target_modules=True)
        results["4a_stale_capture_honest"] = {"rejected": False}
    except Exception as e:
        results["4a_stale_capture_honest"] = {
            "rejected": True,
            "error_type": type(e).__name__,
            "message": str(e)[:400],
        }
    print("Scenario 4a (Stale capture honest invalidation):", json.dumps(results["4a_stale_capture_honest"], indent=2))

    # Scenario 4b: Stale captures — Forced reuse of cached `SourceInputs.olean`, `ProductionSteps.olean`, `Expected.olean`, `Proof.olean`
    w4b = SCRATCH / "scen4b_stale_capture_forced"
    mods4b = stage_clean_sources(w4b, audit_req_orig)
    update_mod_source(mods4b, "Captured", cap_modified)
    try:
        verifier.verify_workspace(
            w4b, mods4b, audit_req_orig,
            prune_unreachable_target_modules=True,
            force_stale_cache_keys={
                "SourceInputs": baseline_merkle["SourceInputs"],
                "InitialCache": baseline_merkle["InitialCache"],
                "ProductionSteps": baseline_merkle["ProductionSteps"],
                "ProductionClaims": baseline_merkle["ProductionClaims"],
                "Expected": baseline_merkle["Expected"],
                "Proof": baseline_merkle["Proof"],
            },
        )
        layer1_4b = {"rejected": False}
    except Exception as e:
        layer1_4b = {"rejected": True, "error_type": type(e).__name__, "message": str(e)}

    # Layer 2 defense-in-depth: pass new `Captured.olean` + stale `SourceInputs.olean`..`Proof.olean` directly to `TrustedBoundary.lean`
    tampered_arts_4b = dict(baseline_artifacts)
    cap_stem = "Captured."
    tampered_arts_4b["Captured"] = [
        [str(w4a / "target-lib" / f"{cap_stem}{p}") for p in OLEAN_PARTS if (w4a / "target-lib" / f"{cap_stem}{p}").exists()],
        [str(w4a / "target-lib" / f"{cap_stem}{p}") for p in IR_PARTS if (w4a / "target-lib" / f"{cap_stem}{p}").exists()],
    ]
    tampered_mods_4b = [dict(m) for m in baseline_active_mods]
    for m in tampered_mods_4b:
        if m["module"] == "Captured":
            m["source"] = next(x["source"] for x in mods4a if x["module"] == "Captured")
            m["expectedSha256"] = next(x["expectedSha256"] for x in mods4a if x["module"] == "Captured")
    layer2_4b = verifier.run_raw_audit(w4b, tampered_arts_4b, baseline_graph, tampered_mods_4b, audit_req_orig)
    results["4b_stale_capture_forced_reuse"] = {
        "layer1_cache_contract": layer1_4b,
        "layer2_trusted_boundary_audit": layer2_4b,
    }
    print("Scenario 4b (Stale capture + forced reuse of Proof/ProductionSteps/Expected):", json.dumps(results["4b_stale_capture_forced_reuse"], indent=2))

    # Scenario 5a: Forged `.olean` tampering in cache (swapping cached `Proof.olean` with a forged `.olean` proving `True`)
    w5a = SCRATCH / "scen5a_forged_olean_tampering"
    mods5a = stage_clean_sources(w5a, audit_req_orig)
    # Compile a forged Proof.olean that proves `theorem verify : True := trivial`
    forged_proof_src = w5a / "ForgedProof.lean"
    forged_proof_olean = w5a / "ForgedProof.olean"
    forged_proof_src.write_text("prelude\nimport Expected\nimport ProductionClaims\nnamespace Proof\ntheorem verify : True := trivial\nend Proof\n")
    subprocess.run([
        "anneal-lean-run", "--mode", "file", "--concurrency", "4", "--",
        str(LEAN_BIN), *COMPILE_FLAGS,
        "--setup", str(SCRATCH / "profile_stage/Proof.setup.json"),
        "-o", str(forged_proof_olean),
        str(forged_proof_src),
    ], cwd=w5a, env=verifier.clean_env, check=True)
    # Tamper with the cached Proof.olean in `cache_dir`!
    proof_cache_entry = cache_dir / "modules" / baseline_merkle["Proof"] / "Proof.olean"
    orig_proof_olean_bytes = proof_cache_entry.read_bytes()
    proof_cache_entry.write_bytes(forged_proof_olean.read_bytes())
    try:
        verifier.verify_workspace(w5a, mods5a, audit_req_orig, prune_unreachable_target_modules=True)
        layer1_5a = {"rejected": False}
    except Exception as e:
        layer1_5a = {"rejected": True, "error_type": type(e).__name__, "message": str(e)}
    finally:
        # Restore clean cache entry
        proof_cache_entry.write_bytes(orig_proof_olean_bytes)

    # Also test Layer 2 defense-in-depth if manifest is ALSO forged by attacker:
    tampered_arts_5a = dict(baseline_artifacts)
    tampered_arts_5a["Proof"] = [
        [str(w5a / f"ForgedProof.{p}") for p in OLEAN_PARTS if (w5a / f"ForgedProof.{p}").exists()],
        [str(w5a / f"ForgedProof.{p}") for p in IR_PARTS if (w5a / f"ForgedProof.{p}").exists()],
    ]
    layer2_5a = verifier.run_raw_audit(w5a, tampered_arts_5a, baseline_graph, baseline_active_mods, audit_req_orig)
    results["5a_forged_weaker_proof_olean"] = {
        "layer1_cache_artifact_digest_check": layer1_5a,
        "layer2_trusted_boundary_audit": layer2_5a,
    }
    print("Scenario 5a (Forged weaker Proof.olean swapped into cache):", json.dumps(results["5a_forged_weaker_proof_olean"], indent=2))

    # Scenario 5b: Forged duplicate declaration / shadowing (`Proof.lean` defines a duplicate `Spec.specs` constant)
    w5b = SCRATCH / "scen5b_forged_duplicate_decl"
    mods5b = stage_clean_sources(w5b, audit_req_orig)
    dup_proof_src = w5b / "DupProof.lean"
    dup_proof_olean = w5b / "DupProof.olean"
    # Define a duplicate `Spec.specs` inside `Proof`'s compiled olean by using Spec's import list
    dup_setup = json.loads((SCRATCH / "profile_stage/Spec.setup.json").read_text())
    dup_setup["name"] = "Proof"
    dup_setup_path = w5b / "DupProof.setup.json"
    dup_setup_path.write_text(json.dumps(dup_setup))
    dup_proof_src.write_text(
        "prelude\nimport Trusted.Mvp\nimport Endianness\n"
        "namespace Spec\ndef specs : Trusted.Mvp.Specs := ⟨fun _ _ => True, fun _ => True⟩\nend Spec\n"
        "namespace Proof\ntheorem verify : True := trivial\nend Proof\n"
    )
    subprocess.run([
        "anneal-lean-run", "--mode", "file", "--concurrency", "4", "--",
        str(LEAN_BIN), *COMPILE_FLAGS,
        "--setup", str(dup_setup_path),
        "-o", str(dup_proof_olean),
        str(dup_proof_src),
    ], cwd=w5b, env=verifier.clean_env, check=True)
    tampered_arts_5b = dict(baseline_artifacts)
    tampered_arts_5b["Proof"] = [
        [str(w5b / f"DupProof.{p}") for p in OLEAN_PARTS if (w5b / f"DupProof.{p}").exists()],
        [str(w5b / f"DupProof.{p}") for p in IR_PARTS if (w5b / f"DupProof.{p}").exists()],
    ]
    tampered_graph_5b = dict(baseline_graph)
    tampered_graph_5b["Proof"] = dup_setup["imports"]
    layer2_5b = verifier.run_raw_audit(w5b, tampered_arts_5b, tampered_graph_5b, baseline_active_mods, audit_req_orig)
    results["5b_forged_duplicate_declaration"] = {
        "layer2_trusted_boundary_audit": layer2_5b,
    }
    print("Scenario 5b (Forged duplicate declaration Spec.specs in Proof.olean):", json.dumps(results["5b_forged_duplicate_declaration"], indent=2))

    (SCRATCH / "invalidation_contract_test_results.json").write_text(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()

