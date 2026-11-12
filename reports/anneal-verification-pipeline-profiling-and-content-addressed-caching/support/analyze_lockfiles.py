#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Static and transitive-closure analysis of foundation-lock.json and library-lock.json."""

import json
import os
from pathlib import Path

MVP_SRC = Path("/tmp/ref_research_stack221_perf/mvp_src")
PREFIX = Path("/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1")
PARTS = ["olean", "olean.server", "olean.private", "ir.sig", "ir"]

def analyze_lock(lock_path: Path, name: str):
    with open(lock_path) as f:
        data = json.load(f)
    modules = data["modules"]
    graph = data["graph"]
    total_modules = len(modules)
    part_counts = {p: 0 for p in PARTS}
    part_bytes = {p: 0 for p in PARTS}
    source_bytes = 0
    total_files_hashed = 0
    total_stat_absent = 0

    for mod, rec in modules.items():
        rel = mod.replace(".", "/")
        src = PREFIX / "src/lean" / f"{rel}.lean"
        if src.exists():
            source_bytes += src.stat().st_size
            total_files_hashed += 1
        for p in PARTS:
            p_path = PREFIX / "lib/lean" / f"{rel}.{p}"
            if rec["parts"].get(p) is not None:
                part_counts[p] += 1
                total_files_hashed += 1
                if p_path.exists():
                    part_bytes[p] += p_path.stat().st_size
            else:
                total_stat_absent += 1

    total_bytes = source_bytes + sum(part_bytes.values())
    return {
        "name": name,
        "total_modules": total_modules,
        "total_files_hashed": total_files_hashed,
        "total_stat_absent": total_stat_absent,
        "source_bytes": source_bytes,
        "part_counts": part_counts,
        "part_bytes": part_bytes,
        "total_bytes": total_bytes,
        "total_mb": total_bytes / (1024 * 1024),
        "data": data,
    }

def compute_closure(roots, f_graph, l_graph):
    visited = set()
    stack = list(roots)
    while stack:
        m = stack.pop()
        if m in visited:
            continue
        visited.add(m)
        for edge in f_graph.get(m, []):
            stack.append(edge["module"])
        for edge in l_graph.get(m, []):
            stack.append(edge["module"])
    return visited

def subset_stats(mod_set, lock_data):
    modules = lock_data["modules"]
    src_b = 0
    part_b = 0
    files = 0
    for mod in mod_set:
        if mod not in modules:
            continue
        rec = modules[mod]
        rel = mod.replace(".", "/")
        src = PREFIX / "src/lean" / f"{rel}.lean"
        if src.exists():
            src_b += src.stat().st_size
            files += 1
        for p in PARTS:
            if rec["parts"].get(p) is not None:
                p_path = PREFIX / "lib/lean" / f"{rel}.{p}"
                if p_path.exists():
                    part_b += p_path.stat().st_size
                    files += 1
    return {
        "modules": len(mod_set),
        "files_hashed": files,
        "source_bytes": src_b,
        "part_bytes": part_b,
        "total_bytes": src_b + part_b,
        "total_mb": (src_b + part_b) / (1024 * 1024),
    }

def main():
    f_lock_path = MVP_SRC / "trusted/lean/foundation-lock.json"
    l_lock_path = MVP_SRC / "trusted/audit/library-lock.json"
    lean_bin = PREFIX / "bin/lean"
    lean_bin_bytes = lean_bin.stat().st_size

    f_res = analyze_lock(f_lock_path, "foundation-lock.json")
    l_res = analyze_lock(l_lock_path, "library-lock.json")
    f_data = f_res.pop("data")
    l_data = l_res.pop("data")

    # Find direct imports of Trusted.*, Anneal.*, and fixtures
    f_graph = f_data["graph"]
    l_graph = l_data["graph"]

    # Check what Init.* modules are imported by Trusted/Mvp and Anneal/Mvp and fixtures
    import re
    def get_imports(paths):
        imps = set()
        for p in paths:
            text = Path(p).read_text()
            imps.update(re.findall(r"^import\s+([A-Za-z0-9_.]+)", text, re.M))
        return sorted(imps)

    trusted_files = sorted((MVP_SRC / "trusted/lean").glob("**/*.lean"))
    theory_files = sorted((MVP_SRC / "theory").glob("**/*.lean"))
    scalar_files = sorted(Path("/tmp/ref_research_stack221_perf/fixtures/scalar/lean").glob("*.lean"))
    spin_files = sorted(Path("/tmp/ref_research_stack221_perf/fixtures/spin/lean").glob("*.lean"))
    starnix_files = sorted(Path("/tmp/ref_research_stack221_perf/fixtures/starnix/proof").glob("*.lean"))

    closures = {}
    for label, roots in [
        ("Init.Prelude_only", ["Init.Prelude"]),
        ("trusted_lean_only", get_imports(trusted_files)),
        ("trusted_plus_theory", get_imports(trusted_files + theory_files)),
        ("fixture_scalar_all_modules", get_imports(trusted_files + theory_files + scalar_files)),
        ("fixture_spin_all_modules", get_imports(trusted_files + theory_files + spin_files)),
        ("fixture_starnix_all_modules", get_imports(trusted_files + theory_files + starnix_files)),
    ]:
        cl = compute_closure(roots, f_graph, l_graph)
        f_cl = cl & set(f_data["modules"].keys())
        l_cl = cl & set(l_data["modules"].keys())
        missing_f = sorted(set(f_data["modules"].keys()) - f_cl)
        missing_l = sorted(set(l_data["modules"].keys()) - l_cl)
        closures[label] = {
            "direct_imports": roots,
            "foundation": subset_stats(f_cl, f_data),
            "foundation_unreached": missing_f,
            "library": subset_stats(l_cl, l_data),
            "library_unreached_count": len(missing_l),
        }

    out = {
        "lean_binary_bytes": lean_bin_bytes,
        "lean_binary_mb": lean_bin_bytes / (1024 * 1024),
        "foundation_lock": f_res,
        "library_lock": l_res,
        "closures": closures,
    }
    print(json.dumps(out, indent=2))

if __name__ == "__main__":
    main()
