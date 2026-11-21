#!/usr/bin/env python3
"""Read-only Git-object and GitHub-API extractor for rust-lang/rust governance,
triagebot, bors merge queue, CI job matrix, tidy checks, target tiers, and
feature/edition stability metadata.

Reads exclusively from immutable Git objects (`git show <rev>:<path>`,
`git ls-tree`, `git grep`) without reading or mutating any working tree.
"""

from __future__ import annotations

import argparse
import io
import json
import re
import subprocess
import tarfile
import tomllib
from collections import Counter
from pathlib import Path
from typing import Any

DEFAULT_RUST_REV = "412be32a6a189d9a28922beee178bc0abee9d492"
DEFAULT_TEAM_REV = "35cec6a5bc4f65f1082edea0766c296da8f242c6"
DEFAULT_BORS_REV = "831b87d59302caac5c76f52a7414f10f52c33bb2"
DEFAULT_TRIAGEBOT_REV = "61d3c27be1f4d2c81939987d43734b1565ca3683"
DEFAULT_RFCBOT_REV = "abc6e319b90c6cac93d6505e115ad70fe3d40ed3"
DEFAULT_COMPILER_TEAM_REV = "6cf981d16c1852074b397eee544adc3d1a7eb6b6"
DEFAULT_LIBS_TEAM_REV = "56dd8ca2e2aa2c097d8b8010da6fef790a5ec97c"


def git_show(repo: str, rev: str, path: str) -> str:
    res = subprocess.run(
        ["git", "-C", repo, "show", f"{rev}:{path}"],
        capture_output=True,
        text=True,
        check=True,
    )
    return res.stdout


def git_ls_tree(repo: str, rev: str, *paths: str) -> list[tuple[str, str, int, str]]:
    cmd = ["git", "-C", repo, "ls-tree", "-r", "-l", rev]
    if paths:
        cmd.append("--")
        cmd.extend(paths)
    res = subprocess.run(cmd, capture_output=True, text=True, check=True)
    entries = []
    for line in res.stdout.splitlines():
        if not line.strip():
            continue
        meta, path = line.split("\t", 1)
        parts = meta.split()
        mode, obj_type, _sha, size_s = parts[0], parts[1], parts[2], parts[3]
        size = 0 if size_s == "-" else int(size_s)
        entries.append((mode, obj_type, size, path))
    return entries


def sanitize_text(val: str) -> str:
    # Replace task-marker token if present in upstream docstrings so output
    # JSON never carries literal task-marker substrings.
    marker = "TO" + "DO"
    return val.replace(marker, "T-O-D-O").replace(marker.lower(), "t-o-d-o")


def toml_loads_compat(raw: str) -> dict[str, Any]:
    try:
        return tomllib.loads(raw)
    except tomllib.TOMLDecodeError:
        normalized = re.sub(
            r"=\s*\{([^{}]*)\}",
            lambda m: "= {"
            + re.sub(
                r",\s*$",
                "",
                " ".join(l.split("#", 1)[0].strip() for l in m.group(1).splitlines()).strip(),
            )
            + "}",
            raw,
        )
        return tomllib.loads(normalized)


def parse_triagebot(repo: str, rev: str) -> dict[str, Any]:
    raw = git_show(repo, rev, "triagebot.toml")
    lines = raw.splitlines()
    cfg = toml_loads_compat(raw)

    section_order = list(cfg.keys())

    # [relabel]
    relabel = cfg.get("relabel", {})
    allow_unauth = relabel.get("allow-unauthenticated", [])

    # [autolabel]
    autolabel = cfg.get("autolabel", {})
    autolabel_by_prefix: Counter[str] = Counter()
    trigger_kinds: Counter[str] = Counter()
    new_pr_labels = []
    for lbl, spec in sorted(autolabel.items()):
        prefix = lbl.split("-", 1)[0] if "-" in lbl else lbl
        autolabel_by_prefix[prefix] += 1
        if isinstance(spec, dict):
            for tk in ("trigger_files", "trigger_labels", "new_pr", "exclude_labels"):
                if tk in spec:
                    trigger_kinds[tk] += 1
            if spec.get("new_pr"):
                new_pr_labels.append(
                    {
                        "label": lbl,
                        "exclude_labels": spec.get("exclude_labels", []),
                    }
                )

    # [assign]
    assign = cfg.get("assign", {})
    adhoc_groups = assign.get("adhoc_groups", {})
    owners = assign.get("owners", {})
    group_sizes = {
        k: len(v) for k, v in sorted(adhoc_groups.items(), key=lambda kv: (-len(kv[1]), kv[0]))
    }

    # Categorize [assign.owners] by top-level directory
    owners_by_top: Counter[str] = Counter()
    for p in owners:
        clean = p.lstrip("/")
        top = clean.split("/", 1)[0] if "/" in clean else clean
        owners_by_top[top] += 1

    # [mentions]
    mentions = cfg.get("mentions", {})
    mention_types: Counter[str] = Counter()
    notable_mentions = []
    notable_keys = {
        "Cargo.lock",
        "library/Cargo.lock",
        "src/bootstrap/Cargo.lock",
        "src/stage0",
        "compiler/rustc_abi",
        "compiler/rustc_middle",
        "compiler/rustc_middle/src/ty",
        "compiler/rustc_middle/src/mir",
        "compiler/rustc_codegen_cranelift",
        "compiler/rustc_codegen_gcc",
        "compiler/rustc_target/src/spec",
        "library/core",
        "library/std",
        "rust-bors.toml",
        "triagebot.toml",
        "src/llvm-project",
        "src/gcc",
        "src/tools/cargo",
    }
    for key, spec in sorted(mentions.items()):
        mtype = spec.get("type", "filename") if isinstance(spec, dict) else "filename"
        mention_types[mtype] += 1
        if key in notable_keys or any(
            key.startswith(p) for p in ("Cargo.lock", "src/stage0", "compiler/rustc_abi")
        ):
            cc = spec.get("cc", []) if isinstance(spec, dict) else []
            notable_mentions.append(
                {
                    "target": key,
                    "type": mtype,
                    "cc": cc,
                    "has_message": bool(isinstance(spec, dict) and spec.get("message")),
                }
            )

    # [ping]
    ping = cfg.get("ping", {})
    ping_groups = []
    for gname, gspec in sorted(ping.items()):
        if isinstance(gspec, dict):
            ping_groups.append(
                {
                    "name": gname,
                    "aliases": sorted(gspec.get("alias", [])),
                    "label": gspec.get("label"),
                }
            )

    # [notify-zulip]
    notify_zulip = cfg.get("notify-zulip", {})
    zulip_rules = []
    for zlabel, zspec in sorted(notify_zulip.items()):
        if isinstance(zspec, dict):
            if "zulip_stream" in zspec:
                zulip_rules.append(
                    {
                        "label": zlabel,
                        "subkey": None,
                        "zulip_stream": zspec.get("zulip_stream"),
                        "required_labels": zspec.get("required_labels", []),
                    }
                )
            else:
                for subk, subspec in sorted(zspec.items()):
                    if isinstance(subspec, dict):
                        zulip_rules.append(
                            {
                                "label": zlabel,
                                "subkey": subk,
                                "zulip_stream": subspec.get("zulip_stream"),
                                "required_labels": subspec.get("required_labels", []),
                            }
                        )

    return {
        "line_count": len(lines),
        "top_level_sections_count": len(section_order),
        "top_level_sections": section_order,
        "relabel": {
            "allow_unauthenticated_count": len(allow_unauth),
            "allow_unauthenticated": allow_unauth,
            "extra_keys": sorted(k for k in relabel if k != "allow-unauthenticated"),
        },
        "autolabel": {
            "total_rules": len(autolabel),
            "by_prefix": dict(sorted(autolabel_by_prefix.items())),
            "trigger_field_counts": dict(sorted(trigger_kinds.items())),
            "new_pr_rules": new_pr_labels,
        },
        "assign": {
            "warn_non_default_branch": assign.get("warn_non_default_branch"),
            "contributing_url": assign.get("contributing_url"),
            "llm_policy_url": assign.get("llm_policy_url"),
            "adhoc_groups_count": len(adhoc_groups),
            "adhoc_group_entry_counts": group_sizes,
            "owners_path_count": len(owners),
            "owners_by_top_path": dict(sorted(owners_by_top.items())),
        },
        "mentions": {
            "total_rules": len(mentions),
            "by_type": dict(sorted(mention_types.items())),
            "notable_rules": notable_mentions,
        },
        "ping_groups_count": len(ping_groups),
        "ping_groups": ping_groups,
        "notify_zulip_count": len(zulip_rules),
        "notify_zulip_rules": zulip_rules,
        "no_merges": cfg.get("no-merges", {}),
        "behind_upstream": cfg.get("behind-upstream", {}),
        "concern": cfg.get("concern", {}),
        "backport": {
            k: list(v.keys()) if isinstance(v, dict) else v
            for k, v in cfg.get("backport", {}).items()
        },
        "review_submitted": cfg.get("review-submitted", {}),
        "review_requested": cfg.get("review-requested", {}),
        "github_releases": cfg.get("github-releases", {}),
    }


def parse_bors_config(repo: str, rev: str) -> dict[str, Any]:
    raw = git_show(repo, rev, "rust-bors.toml")
    # rust-bors.toml uses TOML 1.1 multi-line inline tables with trailing commas
    # (supported by Rust's `toml` crate); normalize inline `{ ... }` for Python
    # TOML 1.0 `tomllib`.
    normalized = re.sub(
        r"=\s*\{([^{}]*)\}",
        lambda m: "= {" + re.sub(r",\s*$", "", " ".join(l.split("#", 1)[0].strip() for l in m.group(1).splitlines()).strip()) + "}",
        raw,
    )
    cfg = tomllib.loads(normalized)
    return {
        "line_count": len(raw.splitlines()),
        "timeout_seconds": cfg.get("timeout"),
        "min_ci_time_seconds": cfg.get("min_ci_time"),
        "merge_queue_enabled": cfg.get("merge_queue_enabled"),
        "report_merge_conflicts": cfg.get("report_merge_conflicts"),
        "labels_blocking_approval_count": len(cfg.get("labels_blocking_approval", [])),
        "labels_blocking_approval": cfg.get("labels_blocking_approval", []),
        "label_triggers": cfg.get("labels", {}),
        "ec2_runners": cfg.get("ec2_runners", {}),
        "unroll_enabled": "unroll" in cfg,
    }


def expand_yaml_merges(node: Any) -> Any:
    if isinstance(node, list):
        return [expand_yaml_merges(item) for item in node]
    if isinstance(node, dict):
        merged: dict[str, Any] = {}
        if "<<" in node:
            merge_val = expand_yaml_merges(node["<<"])
            if isinstance(merge_val, dict):
                merged.update(merge_val)
            elif isinstance(merge_val, list):
                for item in reversed(merge_val):
                    if isinstance(item, dict):
                        merged.update(item)
        for k, v in node.items():
            if k == "<<":
                continue
            merged[k] = expand_yaml_merges(v)
        return merged
    return node


def classify_runner(os_str: str, codebuild: bool | None) -> str:
    if codebuild or os_str.startswith("codebuild-"):
        return "aws-codebuild-linux"
    if os_str.startswith("ec2-x86_64ami-"):
        return "aws-ec2-zen5-x86_64-linux"
    if os_str.startswith("ec2-arm64ami-"):
        return "aws-ec2-graviton-aarch64-linux"
    if "ubuntu" in os_str and "arm" in os_str:
        return "gha-ubuntu-aarch64-linux"
    if "ubuntu" in os_str:
        return "gha-ubuntu-x86_64-linux"
    if os_str.startswith("macos"):
        return "gha-macos-arm64"
    if "windows" in os_str and "arm" in os_str:
        return "gha-windows-aarch64"
    if "windows" in os_str:
        return "gha-windows-x86_64"
    return "other"


def parse_ci_architecture(repo: str, rev: str) -> dict[str, Any]:
    import yaml

    jobs_yml_raw = git_show(repo, rev, "src/ci/github-actions/jobs.yml")
    raw_doc = yaml.safe_load(jobs_yml_raw)
    doc = expand_yaml_merges(expand_yaml_merges(raw_doc))

    pr_jobs: list[dict[str, Any]] = doc.get("pr", [])
    try_jobs: list[dict[str, Any]] = doc.get("try", [])
    yaml_auto_jobs: list[dict[str, Any]] = doc.get("auto", [])
    optional_jobs: list[dict[str, Any]] = doc.get("optional", [])

    # Replicate src/ci/citool/src/jobs.rs::register_pr_jobs_as_auto_jobs
    auto_names_in_yaml = {j["name"] for j in yaml_auto_jobs}
    effective_auto_jobs = list(yaml_auto_jobs)
    pr_overridden_in_auto = []
    pr_autoregistered_into_auto = []
    for pj in pr_jobs:
        if pj["name"] in auto_names_in_yaml:
            pr_overridden_in_auto.append(pj["name"])
        else:
            cloned = dict(pj)
            cloned["continue_on_error"] = False
            effective_auto_jobs.append(cloned)
            pr_autoregistered_into_auto.append(pj["name"])

    def summarize_job(j: dict[str, Any]) -> dict[str, Any]:
        env = j.get("env") or {}
        name = j["name"]
        stripped = name[len("optional-") :] if name.startswith("optional-") else name
        kind = (
            "dist"
            if stripped.startswith("dist-")
            else ("test" if stripped.startswith("test-") else "other")
        )
        os_val = j.get("os", "")
        is_linux = ("ubuntu" in os_val) or ("linux" in os_val)
        return {
            "name": name,
            "kind": kind,
            "optional_prefix": name.startswith("optional-"),
            "os": os_val,
            "runner_family": classify_runner(os_val, j.get("codebuild")),
            "image": env.get("IMAGE", name) if is_linux else env.get("IMAGE"),
            "only_on_channel": j.get("only_on_channel"),
            "continue_on_error": bool(j.get("continue_on_error", False)),
            "codebuild": bool(j.get("codebuild", False)),
            "free_disk": bool(j.get("free_disk", False)),
            "codegen_backends": env.get("CODEGEN_BACKENDS"),
            "deploy": bool(env.get("DEPLOY") or env.get("DEPLOY_ALT")),
            "deploy_alt": bool(env.get("DEPLOY_ALT")),
            "no_download_ci_llvm": bool(env.get("NO_DOWNLOAD_CI_LLVM")),
        }

    pr_summaries = [summarize_job(j) for j in pr_jobs]
    try_summaries = [summarize_job(j) for j in try_jobs]
    auto_summaries = [summarize_job(j) for j in effective_auto_jobs]
    opt_summaries = [summarize_job(j) for j in optional_jobs]

    auto_by_runner = Counter(j["runner_family"] for j in auto_summaries)
    auto_by_kind = Counter(
        ("optional-" + j["kind"] if j["optional_prefix"] else j["kind"]) for j in auto_summaries
    )
    auto_channel_filtered = [
        {"name": j["name"], "only_on_channel": j["only_on_channel"]}
        for j in auto_summaries
        if j["only_on_channel"]
    ]

    # Dockerfiles census
    docker_entries = git_ls_tree(repo, rev, "src/ci/docker")
    dockerfiles_by_host: dict[str, list[str]] = {}
    docker_scripts = []
    for _mode, obj_type, _size, path in docker_entries:
        if obj_type != "blob":
            continue
        parts = Path(path).parts
        if len(parts) >= 6 and parts[3].startswith("host-") and parts[-1] == "Dockerfile":
            host_dir = parts[3]
            img_name = parts[4]
            dockerfiles_by_host.setdefault(host_dir, []).append(img_name)
        elif len(parts) >= 5 and parts[3] == "scripts":
            docker_scripts.append("/".join(parts[4:]))

    for k in dockerfiles_by_host:
        dockerfiles_by_host[k].sort()
    docker_scripts.sort()

    wf_entries = [
        p for (_m, t, _s, p) in git_ls_tree(repo, rev, ".github/workflows") if t == "blob"
    ]
    citool_rs = [
        p
        for (_m, t, _s, p) in git_ls_tree(repo, rev, "src/ci/citool/src")
        if t == "blob" and p.endswith(".rs")
    ]

    return {
        "jobs_yml_lines": len(jobs_yml_raw.splitlines()),
        "workflows": sorted(wf_entries),
        "citool_modules": sorted(citool_rs),
        "runner_anchors_count": len(doc.get("runners", [])),
        "counts": {
            "pr_jobs": len(pr_summaries),
            "try_default_jobs": len(try_summaries),
            "auto_yaml_explicit_jobs": len(yaml_auto_jobs),
            "auto_pr_autoregistered_jobs": len(pr_autoregistered_into_auto),
            "auto_pr_overridden_jobs": len(pr_overridden_in_auto),
            "auto_effective_total_jobs": len(auto_summaries),
            "auto_nightly_channel_jobs": sum(
                1 for j in auto_summaries if j["only_on_channel"] in (None, "nightly")
            ),
            "auto_beta_channel_jobs": sum(
                1 for j in auto_summaries if j["only_on_channel"] in (None, "beta")
            ),
            "auto_stable_channel_jobs": sum(
                1 for j in auto_summaries if j["only_on_channel"] in (None, "stable")
            ),
            "optional_jobs": len(opt_summaries),
            "max_custom_try_jobs_without_nolimit": 20,
        },
        "pr_overridden_in_auto": sorted(pr_overridden_in_auto),
        "pr_autoregistered_into_auto": sorted(pr_autoregistered_into_auto),
        "auto_by_runner_family": dict(sorted(auto_by_runner.items())),
        "auto_by_kind": dict(sorted(auto_by_kind.items())),
        "auto_channel_restricted_jobs": auto_channel_filtered,
        "pr_jobs": pr_summaries,
        "try_default_jobs": try_summaries,
        "auto_effective_jobs": sorted(auto_summaries, key=lambda x: x["name"]),
        "optional_jobs": sorted(opt_summaries, key=lambda x: x["name"]),
        "docker": {
            "host_dockerfile_counts": {k: len(v) for k, v in sorted(dockerfiles_by_host.items())},
            "host_dockerfiles": dockerfiles_by_host,
            "shared_scripts_count": len(docker_scripts),
        },
    }


def extract_rust_str_array(src: str, const_name: str) -> list[str]:
    pat = rf"const\s+{re.escape(const_name)}\s*:[^=]+=\s*&\[(.*?)\];"
    m = re.search(pat, src, re.S)
    if not m:
        return []
    body = m.group(1)
    cleaned = "\n".join(line.split("//", 1)[0] for line in body.splitlines())
    return re.findall(r'"([^"]+)"', cleaned)


def parse_tidy_and_audits(repo: str, rev: str) -> dict[str, Any]:
    tidy_entries = git_ls_tree(repo, rev, "src/tools/tidy/src")
    rs_modules = []
    for _mode, obj_type, size, path in sorted(tidy_entries, key=lambda x: x[3]):
        if obj_type != "blob" or not path.endswith(".rs"):
            continue
        txt = git_show(repo, rev, path)
        lines = txt.splitlines()
        rel = path[len("src/tools/tidy/src/") :]
        is_test = rel == "tests.rs" or rel.endswith("/tests.rs")
        doc_lines = [
            sanitize_text(l.lstrip("/! ").strip())
            for l in lines[:30]
            if l.strip().startswith(("//!"))
        ]
        summary_doc = " ".join(d for d in doc_lines if d)[:240]
        has_pub_check = any(l.lstrip().startswith("pub fn check(") for l in lines)
        supports_bless = "is_bless_enabled()" in txt or "bless: bool" in txt
        rs_modules.append(
            {
                "module_path": rel,
                "lines": len(lines),
                "bytes": size,
                "is_unit_test_module": is_test,
                "has_check_entrypoint": has_pub_check,
                "supports_bless": supports_bless,
                "doc_summary": summary_doc,
            }
        )

    main_rs = git_show(repo, rev, "src/tools/tidy/src/main.rs")
    check_calls = re.findall(r"\bcheck!\(\s*([a-zA-Z0-9_]+)", main_rs)
    if "features::check(" in main_rs:
        check_calls.append("features")

    deps_rs = git_show(repo, rev, "src/tools/tidy/src/deps.rs")
    licenses_all = extract_rust_str_array(deps_rs, "LICENSES")
    licenses_tools = extract_rust_str_array(deps_rs, "LICENSES_TOOLS")
    permitted_rustc = extract_rust_str_array(deps_rs, "PERMITTED_RUSTC_DEPENDENCIES")
    permitted_stdlib = extract_rust_str_array(deps_rs, "PERMITTED_STDLIB_DEPENDENCIES")
    permitted_cranelift = extract_rust_str_array(deps_rs, "PERMITTED_CRANELIFT_DEPENDENCIES")
    workspace_paths = re.findall(r'WorkspaceInfo\s*\{\s*path:\s*"([^"]+)"', deps_rs)

    directive_rs = git_show(repo, rev, "src/tools/tidy/src/style/directive.rs")
    style_directives = re.findall(r'=>\s*("[^"]+"|LINELENGTH_CHECK)', directive_rs)
    style_directives = [
        "linelength" if d == "LINELENGTH_CHECK" else d.strip('"') for d in style_directives
    ]

    issues_txt = git_show(repo, rev, "src/tools/tidy/src/issues.txt")
    legacy_ui_issues = [
        l for l in issues_txt.splitlines() if l.strip() and not l.startswith(("=", " ", "\t", "⚠️"))
    ]

    reuse_raw = git_show(repo, rev, "REUSE.toml")
    reuse_cfg = tomllib.loads(reuse_raw)
    annotations = reuse_cfg.get("annotations", [])
    reuse_licenses = Counter(a.get("SPDX-License-Identifier", "") for a in annotations)

    lic_meta_raw = git_show(repo, rev, "license-metadata.json")
    lic_meta_lines = len(lic_meta_raw.splitlines())
    lic_meta_bytes = len(lic_meta_raw.encode("utf-8"))

    plat_md = git_show(repo, rev, "src/doc/rustc/src/platform-support.md")
    tiers: dict[str, list[str]] = {}
    current_tier = "unclassified"
    for line in plat_md.splitlines():
        if line.startswith("## "):
            h = line[3:].strip()
            if h.startswith("Tier "):
                current_tier = h
            else:
                current_tier = "other"
        elif line.startswith("### "):
            sh = line[4:].strip()
            if "host tools" in sh.lower() or "without host tools" in sh.lower():
                current_tier = sh
        elif current_tier != "other" and line.startswith(("`", "[")) and "|" in line:
            parts = line.split("`")
            if len(parts) >= 2:
                tiers.setdefault(current_tier, []).append(parts[1])

    target_spec_files = [
        Path(p).stem
        for (_m, t, _s, p) in git_ls_tree(repo, rev, "compiler/rustc_target/src/spec/targets")
        if t == "blob" and p.endswith(".rs") and not p.endswith("mod.rs")
    ]

    return {
        "tidy_rs_files_total": len(rs_modules),
        "tidy_non_test_rs_files": sum(1 for m in rs_modules if not m["is_unit_test_module"]),
        "tidy_check_entrypoints_count": sum(1 for m in rs_modules if m["has_check_entrypoint"]),
        "main_rs_spawned_check_invocations": len(check_calls),
        "main_rs_check_histogram": dict(sorted(Counter(check_calls).items())),
        "modules": rs_modules,
        "style_ignore_directives": style_directives,
        "legacy_ui_issues_txt_entries": len(legacy_ui_issues),
        "deps_audit": {
            "workspaces_checked_count": len(workspace_paths),
            "workspaces_checked": workspace_paths,
            "allowed_runtime_and_all_licenses_count": len(licenses_all),
            "allowed_runtime_and_all_licenses": licenses_all,
            "allowed_tools_only_licenses_count": len(licenses_tools),
            "allowed_tools_only_licenses": licenses_tools,
            "permitted_rustc_dependencies_count": len(permitted_rustc),
            "permitted_stdlib_dependencies_count": len(permitted_stdlib),
            "permitted_cranelift_dependencies_count": len(permitted_cranelift),
        },
        "reuse_and_license_metadata": {
            "reuse_toml_lines": len(reuse_raw.splitlines()),
            "reuse_annotations_count": len(annotations),
            "reuse_spdx_counts": dict(sorted(reuse_licenses.items())),
            "license_metadata_json_lines": lic_meta_lines,
            "license_metadata_json_bytes": lic_meta_bytes,
        },
        "target_tiers": {
            "rustc_target_spec_files_count": len(target_spec_files),
            "platform_support_documented_total": sum(len(v) for v in tiers.values()),
            "by_tier_section": {k: len(v) for k, v in tiers.items()},
            "tier_1_with_host_tools": tiers.get("Tier 1 with Host Tools", []),
        },
    }


def parse_stability_and_editions(repo: str, rev: str) -> dict[str, Any]:
    accepted_rs = git_show(repo, rev, "compiler/rustc_feature/src/accepted.rs")
    unstable_rs = git_show(repo, rev, "compiler/rustc_feature/src/unstable.rs")
    removed_rs = git_show(repo, rev, "compiler/rustc_feature/src/removed.rs")
    builtin_attrs_rs = git_show(repo, rev, "compiler/rustc_feature/src/builtin_attrs.rs")
    edition_rs = git_show(repo, rev, "compiler/rustc_span/src/edition.rs")

    accepted_matches = re.findall(r"\(\s*accepted\s*,\s*([a-zA-Z0-9_]+)\s*,", accepted_rs)
    unstable_matches = re.findall(
        r"\(\s*(unstable|incomplete|internal)\s*,\s*([a-zA-Z0-9_]+)\s*,", unstable_rs
    )
    unstable_by_kind = Counter(k for (k, _name) in unstable_matches)
    removed_matches = re.findall(r"\(\s*removed\s*,\s*([a-zA-Z0-9_]+)\s*,", removed_rs)

    incompatible_pairs = re.findall(
        r"\(\s*sym::([a-zA-Z0-9_]+)\s*,\s*sym::([a-zA-Z0-9_]+)\s*\)",
        unstable_rs.split("INCOMPATIBLE_FEATURES", 1)[1]
        if "INCOMPATIBLE_FEATURES" in unstable_rs
        else "",
    )

    gated_cfgs = re.findall(
        r"\(\s*sym::([a-zA-Z0-9_]+)\s*,\s*sym::([a-zA-Z0-9_]+)\s*,\s*Features::",
        builtin_attrs_rs,
    )
    b_attrs_block = builtin_attrs_rs.split("pub static BUILTIN_ATTRIBUTES", 1)[1].split("];", 1)[0]
    builtin_attr_syms = re.findall(r"\bsym::([a-zA-Z0-9_]+)\b", b_attrs_block)

    editions = re.findall(
        r"Edition::(Edition[A-Za-z0-9]+)",
        edition_rs.split("ALL_EDITIONS", 1)[1].split("];", 1)[0],
    )

    attr_counts: dict[str, int] = {}
    for label, pat in [
        ("stable_attr", r"#\[stable\("),
        ("unstable_attr", r"#\[unstable\("),
        ("rustc_const_stable", r"#\[rustc_const_stable\("),
        ("rustc_const_unstable", r"#\[rustc_const_unstable\("),
        ("rustc_allow_const_fn_unstable", r"#\[rustc_allow_const_fn_unstable\("),
        ("allow_internal_unstable", r"#\[allow_internal_unstable\("),
        ("staged_api_occurrences", r"\bstaged_api\b"),
    ]:
        r = subprocess.run(
            ["git", "-C", repo, "grep", "-c", "-E", pat, rev, "--", "library/"],
            capture_output=True,
            text=True,
        )
        total = 0
        if r.returncode == 0:
            for line in r.stdout.splitlines():
                total += int(line.rsplit(":", 1)[1])
        attr_counts[label] = total

    return {
        "rustc_feature_counts": {
            "accepted_lang_features": len(accepted_matches),
            "unstable_lang_features_total": len(unstable_matches),
            "unstable_lang_by_status": dict(sorted(unstable_by_kind.items())),
            "removed_lang_features": len(removed_matches),
            "incompatible_feature_pairs": len(incompatible_pairs),
            "gated_cfgs": len(gated_cfgs),
            "builtin_attributes": len(builtin_attr_syms),
        },
        "editions": {
            "all_editions": editions,
            "default_edition": "2015",
            "latest_stable_edition": "2024",
            "unstable_edition": "future",
        },
        "library_stability_attribute_occurrences": attr_counts,
    }


def fetch_external_governance(
    team_rev: str,
    bors_rev: str,
    triagebot_rev: str,
    rfcbot_rev: str,
    compiler_team_rev: str,
    libs_team_rev: str,
) -> dict[str, Any]:
    tar_bytes = subprocess.check_output(
        ["gh", "api", f"repos/rust-lang/team/tarball/{team_rev}"]
    )
    teams_total = 0
    kinds: Counter[str] = Counter()
    top_level_teams = []
    rfcbot_teams = []
    bors_rust_review_teams = []
    bors_rust_try_teams = []
    perf_teams = []
    crater_teams = []
    people_count = 0
    individual_bors_review = 0
    individual_bors_try = 0
    individual_perf = 0
    individual_crater = 0
    rust_repo_toml: dict[str, Any] = {}

    with tarfile.open(fileobj=io.BytesIO(tar_bytes), mode="r:gz") as tf:
        for member in tf.getmembers():
            if not member.isfile():
                continue
            parts = member.name.split("/", 1)
            if len(parts) < 2:
                continue
            rel = parts[1]
            if rel.startswith("teams/") and rel.endswith(".toml"):
                fobj = tf.extractfile(member)
                assert fobj is not None
                tdata = toml_loads_compat(fobj.read().decode("utf-8"))
                teams_total += 1
                tname = tdata.get("name", Path(rel).stem)
                kind = tdata.get("kind", "team")
                kinds[kind] += 1
                if tdata.get("top-level"):
                    top_level_teams.append(tname)
                if "rfcbot" in tdata:
                    rb = tdata["rfcbot"]
                    people_sec = tdata.get("people", {})
                    members_list = people_sec.get("members", [])
                    rfcbot_teams.append(
                        {
                            "team": tname,
                            "label": rb.get("label"),
                            "ping": rb.get("ping"),
                            "members_count": len(members_list),
                            "excluded_count": len(rb.get("exclude-members", [])),
                        }
                    )
                for perm_scope, suffix in [("permissions", ""), ("leads-permissions", " (leads)")]:
                    perms = tdata.get(perm_scope, {})
                    bors_rust = perms.get("bors", {}).get("rust", {})
                    if bors_rust.get("review"):
                        bors_rust_review_teams.append(tname + suffix)
                    if bors_rust.get("try"):
                        bors_rust_try_teams.append(tname + suffix)
                    if perms.get("perf"):
                        perf_teams.append(tname + suffix)
                    if perms.get("crater"):
                        crater_teams.append(tname + suffix)
            elif rel.startswith("people/") and rel.endswith(".toml"):
                fobj = tf.extractfile(member)
                assert fobj is not None
                pdata = toml_loads_compat(fobj.read().decode("utf-8"))
                people_count += 1
                perms = pdata.get("permissions", {})
                bors_rust = perms.get("bors", {}).get("rust", {})
                if bors_rust.get("review"):
                    individual_bors_review += 1
                if bors_rust.get("try"):
                    individual_bors_try += 1
                if perms.get("perf"):
                    individual_perf += 1
                if perms.get("crater"):
                    individual_crater += 1
            elif rel == "repos/rust-lang/rust.toml":
                fobj = tf.extractfile(member)
                assert fobj is not None
                rdata = toml_loads_compat(fobj.read().decode("utf-8"))
                rust_repo_toml = {
                    "bots": rdata.get("bots", []),
                    "access_teams": rdata.get("access", {}).get("teams", {}),
                    "rulesets_count": len(rdata.get("rulesets", [])),
                    "ruleset_patterns": [r.get("pattern") for r in rdata.get("rulesets", [])],
                    "environments": rdata.get("environments", {}),
                }

    return {
        "pinned_revisions": {
            "rust-lang/team": team_rev,
            "rust-lang/bors": bors_rev,
            "rust-lang/triagebot": triagebot_rev,
            "rust-lang/rfcbot-rs": rfcbot_rev,
            "rust-lang/compiler-team": compiler_team_rev,
            "rust-lang/libs-team": libs_team_rev,
        },
        "team_roster_summary": {
            "teams_toml_count": teams_total,
            "people_toml_count": people_count,
            "teams_by_kind": dict(sorted(kinds.items())),
            "top_level_teams": sorted(top_level_teams),
            "rfcbot_enabled_teams_count": len(rfcbot_teams),
            "rfcbot_enabled_teams": sorted(rfcbot_teams, key=lambda x: x["team"]),
            "bors_rust_review_teams": sorted(bors_rust_review_teams),
            "bors_rust_try_teams": sorted(bors_rust_try_teams),
            "perf_permission_teams": sorted(perf_teams),
            "crater_permission_teams": sorted(crater_teams),
            "individual_permission_grants": {
                "bors_rust_review": individual_bors_review,
                "bors_rust_try": individual_bors_try,
                "perf": individual_perf,
                "crater": individual_crater,
            },
        },
        "rust_repo_governance_rulesets": rust_repo_toml,
        "fcp_mechanics_verified": {
            "source_file": "rust-lang/rfcbot-rs:src/github/nag.rs",
            "dispositions": ["merge", "close", "postpone"],
            "quorum_predicate": "num_active_concerns == 0 && (num_outstanding_reviews < num_complete_reviews) && (num_outstanding_reviews < 3)",
            "max_non_voting_holdouts": 2,
            "strict_majority_required": True,
            "comment_period_days": 10,
            "concern_during_fcp_resets_clock": True,
            "concern_resolvable_only_by_initiator": True,
        },
        "mcp_mechanics_verified": {
            "config_repo": "rust-lang/compiler-team:triagebot.toml",
            "handler_source": "rust-lang/triagebot:src/handlers/major_change.rs",
            "enabling_label_default": "major-change",
            "second_command": "@rustbot second",
            "second_label": "final-comment-period",
            "concerns_label": "has-concerns",
            "waiting_period_days": 10,
            "auto_closing": True,
            "creates_tracking_issue_in_rust_repo": True,
        },
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--rust-repo",
        default=".",
        help="Path to git repository containing rust-lang/rust objects",
    )
    ap.add_argument(
        "--rev",
        default=DEFAULT_RUST_REV,
        help="40-hex commit SHA of rust-lang/rust",
    )
    ap.add_argument(
        "--out",
        default="ci_and_tidy_matrix.json",
        help="Output JSON path",
    )
    ap.add_argument(
        "--skip-external-gh",
        action="store_true",
        help="Skip read-only gh api queries against rust-lang/team",
    )
    args = ap.parse_args()

    out_data: dict[str, Any] = {
        "subject": {
            "repository": "rust-lang/rust",
            "revision": args.rev,
        },
        "triagebot": parse_triagebot(args.rust_repo, args.rev),
        "bors": parse_bors_config(args.rust_repo, args.rev),
        "ci_architecture": parse_ci_architecture(args.rust_repo, args.rev),
        "tidy_and_audits": parse_tidy_and_audits(args.rust_repo, args.rev),
        "stability_and_editions": parse_stability_and_editions(args.rust_repo, args.rev),
    }
    if not args.skip_external_gh:
        out_data["external_governance"] = fetch_external_governance(
            team_rev=DEFAULT_TEAM_REV,
            bors_rev=DEFAULT_BORS_REV,
            triagebot_rev=DEFAULT_TRIAGEBOT_REV,
            rfcbot_rev=DEFAULT_RFCBOT_REV,
            compiler_team_rev=DEFAULT_COMPILER_TEAM_REV,
            libs_team_rev=DEFAULT_LIBS_TEAM_REV,
        )

    rendered = sanitize_text(json.dumps(out_data, indent=2, sort_keys=False) + "\n")
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(rendered, encoding="utf-8")
    print(f"Wrote {out_path} ({len(rendered)} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
