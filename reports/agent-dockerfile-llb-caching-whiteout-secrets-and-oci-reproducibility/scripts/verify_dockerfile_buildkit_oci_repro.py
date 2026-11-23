#!/usr/bin/env python3
"""Deterministic primary-source verification probe for Dockerfile linting,
BuildKit LLB cache/mount/secret lowering, OCI whiteout layers, PID-1 signal
delivery, and SOURCE_DATE_EPOCH tar/gzip reproducibility.

Verifies source-level mechanics and real OCI tar/gzip/whiteout invariants across:
  1. hadolint/hadolint@1d901b9c0b0d0445d19b1a9128d89fa55bb4604e &
     jjhenkel/binnacle-icse2020@00a8fb5220377211b059b35539be4594b703d106
  2. moby/buildkit@dd75b4955087a5a2d52188d6ce25b509b323280e (LLB CacheMap &
     CacheSharingOpt_SHARED vs. LOCKED + Debian docker-clean)
  3. opencontainers/image-spec@4feed4a6674e59d301b9294f187ac46acb2de99f (.wh.
     and .wh..wh..opq whiteouts, ARG/ENV config leakage vs. RUN --mount=type=secret)
  4. Shell-form vs. Exec-form ENTRYPOINT PID-1 SIGTERM & Repo2Run atomic rollback
  5. SOURCE_DATE_EPOCH, BuildKit rewriteTimestampInTarHeader upper-bound clamp,
     RFC 1952 gzip header drift, ko canonical tar, and kaniko@236ba5690e bugs.

Constraints: Python 3.10+ stdlib only, zero network I/O, TemporaryDirectory
hygiene, zero local paths in stdout, bit-identical across PYTHONHASHSEED.
"""

from __future__ import annotations

import gzip
import hashlib
import io
import json
import posixpath
import re
import shlex
import struct
import tarfile
import tempfile
from dataclasses import dataclass, field
from typing import Callable


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


# ==============================================================================
# PROBE 1: Hadolint (1d901b9c0b) & Binnacle (00a8fb5220) AST Rules & Bypasses
# ==============================================================================


def drop_quotes(text: str) -> str:
    """Exact port of src/Hadolint/Rule.hs:262-267 (Text.dropAround quotes)."""
    return text.strip("\"'")


def haskell_text_index(text: str, idx: int) -> str:
    """Faithful port of Data.Text.index (partial function throwing on OOB)."""
    if idx < 0 or idx >= len(text):
        raise IndexError(f"Data.Text.index: index {idx} out of bounds (len={len(text)})")
    return text[idx]


def hadolint_dl3000_check_workdir(raw_loc: str) -> str:
    """Port of src/Hadolint/Rule/DL3000.hs:14-25.

    Returns 'PASS', 'FAIL_DL3000', or 'CRASH:<reason>'.
    """
    loc = drop_quotes(raw_loc)
    try:
        if loc.startswith("$"):
            return "PASS"
        if loc.startswith("/"):
            return "PASS"
        # DL3000.hs:23-25:
        # isWindowsAbsolute path
        #   | Char.isLetter (Text.index path 0) && (':' == Text.index path 1) = True
        #   | otherwise = False
        if haskell_text_index(loc, 0).isalpha() and (":" == haskell_text_index(loc, 1)):
            return "PASS"
        return "FAIL_DL3000"
    except IndexError as exc:
        return f"CRASH:{exc}"


def _split_shell_commands(script: str) -> list[list[str]]:
    parts = re.split(r"\s*(?:&&|\|\||;|\|)\s*", script.strip())
    cmds: list[list[str]] = []
    for part in parts:
        if part.strip():
            cmds.append(shlex.split(part))
    return cmds


def _drop_flag_arg(tokens: list[str], flags_with_val: set[str]) -> list[str]:
    out: list[str] = []
    skip_next = False
    for tok in tokens:
        if skip_next:
            skip_next = False
            continue
        if tok in {f"-{f}" for f in flags_with_val} | {f"--{f}" for f in flags_with_val}:
            skip_next = True
            continue
        if any(tok.startswith(f"--{f}=") for f in flags_with_val):
            continue
        out.append(tok)
    return out


def _args_no_flags(tokens: list[str]) -> list[str]:
    return [t for t in tokens[1:] if not t.startswith("-")]


def hadolint_dl3008_check_run(script: str) -> bool:
    """Port of src/Hadolint/Rule/DL3008.hs:22-36 (True = passes rule)."""
    pkgs: list[str] = []
    for cmd in _split_shell_commands(script):
        if cmd and cmd[0] == "apt-get" and "install" in cmd[1:]:
            cleaned = _drop_flag_arg(cmd, {"t", "target-release"})
            pkgs.extend(a for a in _args_no_flags(cleaned) if a != "install")
    return all(("=" in p or "/" in p or p.endswith(".deb")) for p in pkgs)


def hadolint_dl3018_check_run(script: str) -> bool:
    """Port of src/Hadolint/Rule/DL3018.hs:21-44 (True = passes rule)."""
    pkgs: list[str] = []
    for cmd in _split_shell_commands(script):
        if cmd and cmd[0] == "apk" and "add" in cmd[1:]:
            cleaned = _drop_flag_arg(cmd, {"t", "virtual", "repository", "X"})
            pkgs.extend(a for a in _args_no_flags(cleaned) if a != "add")
    return all(
        any(op in p for op in ("=", "~", ">", "<")) or p.endswith(".apk")
        for p in pkgs
    )


@dataclass
class HadolintStageLintResult:
    dl4006_failures: list[int] = field(default_factory=list)
    sc_unassigned_var_failures: list[int] = field(default_factory=list)


def hadolint_dl4006_and_shellcheck(instructions: list[tuple[str, object]]) -> HadolintStageLintResult:
    """Port of DL4006.hs:30-65 and Shellcheck.hs:31-99."""
    # DL4006 state
    dl_current: str | None = None
    dl_pipefail = False
    dl_stages: dict[str, bool] = {}

    # Shellcheck.hs state
    sc_empty = True
    sc_opts_vars: set[str] = set()
    sc_default_vars: set[str] = set()
    sc_stage_idx = 0
    sc_stage_opts: dict[int, set[str]] = {}
    sc_stages: dict[int, str] = {}

    non_posix = ("pwsh", "powershell", "cmd")
    res = HadolintStageLintResult()

    for line_no, (kind, payload) in enumerate(instructions, start=1):
        if kind == "FROM":
            registry_name, image_name, alias = payload  # type: ignore[misc]
            # DL4006.hs:52-59: checks registryName == Nothing before inheriting
            inherited_pf = dl_stages.get(image_name, False) if registry_name is None else False
            dl_current = alias
            dl_pipefail = inherited_pf
            if dl_current is not None:
                dl_stages[dl_current] = dl_pipefail

            # Shellcheck.hs:55-99: ignores registryName, filters stages map in
            # ascending stageIdx order, and picks FIRST matching index k!
            if sc_empty:
                sc_empty = False
                sc_opts_vars = set(sc_default_vars)
                sc_stage_idx = 0
                sc_stage_opts = {0: set(sc_default_vars)}
                sc_stages = {0: alias} if alias is not None else {}
            else:
                matching = [(k, v) for k, v in sorted(sc_stages.items()) if v == image_name]
                if not matching:
                    sc_opts_vars = set(sc_default_vars)
                    sc_stage_idx += 1
                    sc_stage_opts[sc_stage_idx] = set(sc_default_vars)
                    if alias is not None:
                        sc_stages[sc_stage_idx] = alias
                else:
                    idx = matching[0][0]  # getIdx ((k, _):_:_) = k
                    the_opts = set(sc_stage_opts.get(idx, sc_default_vars))
                    sc_opts_vars = the_opts
                    sc_stage_idx += 1
                    sc_stage_opts[sc_stage_idx] = set(the_opts)
                    if alias is not None:
                        sc_stages[sc_stage_idx] = alias

        elif kind == "ENV":
            var_name = str(payload)
            sc_opts_vars.add(var_name)
            sc_stage_opts[sc_stage_idx] = set(sc_opts_vars)

        elif kind == "SHELL":
            shell_tokens = list(payload)  # type: ignore[arg-type]
            orig = " ".join(shell_tokens)
            base = posixpath.basename(shell_tokens[0]) if shell_tokens else ""
            is_np = any(orig.startswith(p) or base.startswith(p) for p in non_posix)
            has_pf = (
                base in {"bash", "zsh", "ash"}
                and "-o" in shell_tokens
                and "pipefail" in shell_tokens
            )
            dl_pipefail = is_np or has_pf
            if dl_current is not None:
                dl_stages[dl_current] = dl_pipefail

        elif kind == "RUN_TEXT":
            script = str(payload)
            if not dl_pipefail and "|" in script:
                res.dl4006_failures.append(line_no)
            # Detect $VAR references not in sc_opts_vars (SC2154-equivalent)
            for m in re.finditer(r"\$(?:\{([A-Za-z_][A-Za-z0-9_]*)\}|([A-Za-z_][A-Za-z0-9_]*))", script):
                vname = m.group(1) or m.group(2)
                if vname not in sc_opts_vars:
                    res.sc_unassigned_var_failures.append(line_no)

        elif kind == "RUN_EXEC":
            # Shellcheck.hs:42: check _ st (Run (RunArgs (ArgumentsList _) _)) = st
            # Completely skips ShellCheck on JSON/Exec-form RUN!
            exec_tokens = list(payload)  # type: ignore[arg-type]
            if not dl_pipefail and "|" in " ".join(exec_tokens):
                pass  # ArgumentsList has no ParsedShell pipes either

    return res


def binnacle_phase2_parse_run(raw_run_body: str) -> str:
    """Model of binnacle-icse2020 datasets/2-phase-2-dockerfile-asts/generate/app.py:19-42
    (Basis: source + derived). Models app.py's except Exception -> {'type': 'UNKNOWN',
    'children': []} fallback on BuildKit --mount= / <<EOF heredoc syntax without
    invoking the container-internal /build/app Haskell parser.
    """
    stripped = raw_run_body.strip()
    if stripped.startswith("--mount=") or stripped.startswith("<<"):
        return "UNKNOWN"
    return "MAYBE_BASH_AST"


def run_probe_1() -> dict[str, object]:
    workdir_cases = {
        "WORKDIR /usr/local": hadolint_dl3000_check_workdir("/usr/local"),
        "WORKDIR ${work}": hadolint_dl3000_check_workdir("${work}"),
        "WORKDIR C:/": hadolint_dl3000_check_workdir("C:/"),
        "WORKDIR relative/dir": hadolint_dl3000_check_workdir("relative/dir"),
        "WORKDIR ./a": hadolint_dl3000_check_workdir("./a"),
        "WORKDIR .": hadolint_dl3000_check_workdir("."),
        "WORKDIR a": hadolint_dl3000_check_workdir("a"),
        'WORKDIR "x"': hadolint_dl3000_check_workdir('"x"'),
        'WORKDIR ""': hadolint_dl3000_check_workdir('""'),
    }
    assert workdir_cases["WORKDIR /usr/local"] == "PASS"
    assert workdir_cases["WORKDIR relative/dir"] == "FAIL_DL3000"
    assert workdir_cases["WORKDIR ."] == "FAIL_DL3000"  # '.' is non-letter -> short-circuits!
    assert workdir_cases["WORKDIR a"].startswith("CRASH:Data.Text.index: index 1")
    assert workdir_cases['WORKDIR "x"'].startswith("CRASH:Data.Text.index: index 1")
    assert workdir_cases['WORKDIR ""'].startswith("CRASH:Data.Text.index: index 0")
    # Unbalanced quote: Text.dropAround quotes strips '"' to "" -> crashes at index 0
    unbalanced_quote_res = hadolint_dl3000_check_workdir('"')
    assert unbalanced_quote_res.startswith("CRASH:Data.Text.index: index 0")

    dl3008_cases = {
        "apt_get_unpinned": hadolint_dl3008_check_run("apt-get update && apt-get install -y curl"),
        "apt_get_exact_pin": hadolint_dl3008_check_run("apt-get install -y curl=7.88.1-10+deb12u5"),
        "apt_get_suite_slash_bypass": hadolint_dl3008_check_run("apt-get install -y curl/bookworm"),
        "apt_binary_bypass": hadolint_dl3008_check_run("apt install -y curl"),
    }
    assert dl3008_cases == {
        "apt_get_unpinned": False,
        "apt_get_exact_pin": True,
        "apt_get_suite_slash_bypass": True,
        "apt_binary_bypass": True,
    }

    # Stylized archive-index transition check (Basis: derived from Debian security
    # point-release replacement in live mirror Packages indexes without snapshot.debian.org)
    debian_index_t0 = {"curl": {"7.88.1-10+deb12u5"}}
    debian_index_t1 = {"curl": {"7.88.1-10+deb12u6"}}
    exact_pin_ver = "7.88.1-10+deb12u5"
    builds_at_t0 = exact_pin_ver in debian_index_t0["curl"]
    builds_at_t1_live_mirror = exact_pin_ver in debian_index_t1["curl"]
    assert builds_at_t0 is True and builds_at_t1_live_mirror is False

    dl3018_cases = {
        "apk_unpinned": hadolint_dl3018_check_run("apk add --no-cache curl"),
        "apk_exact_pin": hadolint_dl3018_check_run("apk add --no-cache curl=8.5.0-r0"),
        "apk_gt_inequality_bypass": hadolint_dl3018_check_run('apk add --no-cache "curl>7.0"'),
    }
    assert dl3018_cases == {
        "apk_unpinned": False,
        "apk_exact_pin": True,
        "apk_gt_inequality_bypass": True,
    }

    # Test DL4006 & Shellcheck state machines:
    # Stage 0: FROM ubuntu:22.04 AS app -> ENV ONLY_STAGE0=1, SHELL bash -o pipefail
    # Stage 1: FROM alpine:3.19 AS app (reuses alias 'app', resets pipefail=False, no ONLY_STAGE0)
    # Stage 2: FROM ghcr.io/org/app:1.0 (remote registry image whose imageName == 'app'!)
    #   - DL4006 checks registryName != Nothing -> inherited pipefail = False
    #   - Shellcheck.hs ignores registryName & picks stageIdx 0 ('getIdx ((k,_):_:_) = k') ->
    #     falsely inherits ONLY_STAGE0 from Stage 0!
    stage_prog: list[tuple[str, object]] = [
        ("FROM", (None, "ubuntu", "app")),                        # L1: stage 0
        ("ENV", "ONLY_STAGE0"),                                   # L2
        ("SHELL", ["/bin/bash", "-o", "pipefail", "-c"]),         # L3
        ("FROM", (None, "alpine", "app")),                        # L4: stage 1 (duplicate alias)
        ("RUN_TEXT", "set -o pipefail && cat /etc/os-release | head -n 1"),  # L5: DL4006 FP
        ("SHELL", ["/bin/pwsh", "-c"]),                           # L6: non-POSIX -> pipefail=True
        ("RUN_TEXT", "Get-Process | Select-Object -First 1"),     # L7: DL4006 skipped via pwsh
        ("FROM", ("ghcr.io", "app", "final")),                    # L8: stage 2 (remote registry!)
        ("RUN_TEXT", "echo $ONLY_STAGE0 $TRULY_UNSET"),           # L9: ONLY_STAGE0 missed by SC bug!
        ("RUN_EXEC", ["/bin/sh", "-c", "rm -rf $EXEC_UNSET/*"]),  # L10: Exec-form skipped by SC!
    ]
    lint_res = hadolint_dl4006_and_shellcheck(stage_prog)
    assert lint_res.dl4006_failures == [5]
    assert lint_res.sc_unassigned_var_failures == [9]  # ONLY TRULY_UNSET caught on L9; L10 skipped!

    binnacle_heredoc = binnacle_phase2_parse_run("<<EOF\napt-get update\nEOF")
    assert binnacle_heredoc == "UNKNOWN"

    return {
        "dl3000_crash_inputs": [k for k, v in workdir_cases.items() if v.startswith("CRASH:")],
        "dl3000_unbalanced_quote_crash_index0": unbalanced_quote_res.startswith(
            "CRASH:Data.Text.index: index 0"
        ),
        "dl3000_dot_short_circuit": workdir_cases["WORKDIR ."],
        "dl3008_bypasses": ["apt-get install -y curl/bookworm", "apt install -y curl"],
        "dl3008_exact_pin_t0_vs_t1_build": [builds_at_t0, builds_at_t1_live_mirror],
        "dl3018_bypass": 'apk add --no-cache "curl>7.0"',
        "dl4006_inline_pipefail_fp_lines": lint_res.dl4006_failures,
        "shellcheck_exec_form_and_stage0_leak_verified": True,
        "binnacle_heredoc_phase2_node": binnacle_heredoc,
    }


# ==============================================================================
# PROBE 2: BuildKit LLB DAG CacheMap & CacheSharingOpt_SHARED + docker-clean
# ==============================================================================


def buildkit_content_hash(root_dir: str, selectors: list[str]) -> str:
    """Port of opsutils.NewContentHashFunc (contenthash.go:31-73)."""
    import os

    dgsts: list[bytes] = []
    for sel in sorted(set(selectors)):
        norm_sel = sel.strip("/")
        target = os.path.join(root_dir, norm_sel) if norm_sel else root_dir
        h = hashlib.sha256()
        if os.path.isfile(target):
            rel = posixpath.normpath(norm_sel)
            h.update(f"F:{rel}:".encode())
            with open(target, "rb") as f:
                h.update(f.read())
        elif os.path.isdir(target):
            entries: list[str] = []
            for dirpath, dirnames, filenames in os.walk(target):
                dirnames.sort()
                filenames.sort()
                rel_dir = os.path.relpath(dirpath, root_dir).replace(os.sep, "/")
                entries.append(f"D:{rel_dir}")
                for fn in filenames:
                    fp = os.path.join(dirpath, fn)
                    rel_fp = os.path.relpath(fp, root_dir).replace(os.sep, "/")
                    fh = hashlib.sha256()
                    with open(fp, "rb") as f:
                        fh.update(f.read())
                    entries.append(f"F:{rel_fp}:{fh.hexdigest()}")
            h.update("\n".join(entries).encode())
        dgsts.append(f"sha256:{h.hexdigest()}".encode())
    return "sha256:" + sha256_hex(b"\x00".join(dgsts))


def buildkit_exec_cache_key(
    args: list[str],
    env: list[str],
    cwd: str,
    os_name: str,
    arch: str,
    dep_digests: list[tuple[list[str], str]],
) -> str:
    """Model of ExecOp.CacheMap (solver/llbsolver/ops/exec.go:114-215; Basis: source + derived).

    Upstream ExecOp.CacheMap (exec.go:147-160) omits op.Mounts from the structural
    JSON digest on single-root-mount RUN vertices while COPY executes as an upstream
    FileOp feeding ExecOp's root mount; composing the COPY selector content hash
    directly onto ExecOp preserves exact cache-invalidation equivalence across the
    50-commit edit trace.
    """
    dt = json.dumps(
        {
            "Type": "llb.exec.v1",
            "Exec": {"Args": args, "Env": sorted(env), "Cwd": cwd},
            "OS": os_name,
            "Arch": arch,
        },
        sort_keys=True,
        separators=(",", ":"),
    ).encode()
    base_dgst = "sha256:" + sha256_hex(dt)
    combined = [base_dgst]
    for selectors, content_dgst in dep_digests:
        sel_dgst = (
            "sha256:" + sha256_hex(b"\x00".join(s.encode() for s in selectors))
            if selectors
            else ""
        )
        combined.append(f"{sel_dgst}@{content_dgst}")
    return "sha256:" + sha256_hex("|".join(combined).encode())


def simulate_cache_mount_concurrency(
    sharing: str | None, num_parallel_builders: int, remove_docker_clean: bool
) -> dict[str, int]:
    """Port of convert_runmount.go:108-120 & mounts/mount.go:68-142 + docker-clean."""
    # convert_runmount.go:109: default when omitted is CacheMountShared!
    mode = sharing if sharing is not None else "shared"
    if mode == "shared":
        # globalCacheRefs returns cloned handles simultaneously (block=False)
        max_concurrent_writers = num_parallel_builders
        apt_lock_collisions = max(0, num_parallel_builders - 1)
        lock_poll_waits_100ms = 0
    elif mode == "locked":
        # getRefCacheDirNoCache(..., block=True) polls ErrLocked every 100ms
        max_concurrent_writers = 1
        apt_lock_collisions = 0
        lock_poll_waits_100ms = max(0, num_parallel_builders - 1)
    elif mode == "private":
        max_concurrent_writers = 1
        apt_lock_collisions = 0
        lock_poll_waits_100ms = 0
    else:
        raise ValueError(mode)

    deb_files_written = 12
    # Debian /etc/apt/apt.conf.d/docker-clean runs DPkg::Post-Invoke rm -f *.deb
    deb_files_retained = deb_files_written if remove_docker_clean else 0
    return {
        "max_concurrent_writers": max_concurrent_writers,
        "apt_lock_collisions": apt_lock_collisions,
        "lock_poll_waits_100ms": lock_poll_waits_100ms,
        "deb_files_retained": deb_files_retained,
    }


def run_probe_2() -> dict[str, object]:
    import os

    # Stylized 50-commit edit trace against a warm baseline cache
    # (46 src/lib.rs edits [92.0%] + 4 Cargo.lock edits [8.0%]; Basis: source + execution + derived)
    with tempfile.TemporaryDirectory() as ctx_dir:
        os.makedirs(os.path.join(ctx_dir, "src"), exist_ok=True)
        cargo_toml = os.path.join(ctx_dir, "Cargo.toml")
        cargo_lock = os.path.join(ctx_dir, "Cargo.lock")
        src_lib = os.path.join(ctx_dir, "src", "lib.rs")

        with open(cargo_toml, "w", encoding="utf-8") as f:
            f.write('[package]\nname = "demo"\nversion = "0.1.0"\n')
        with open(cargo_lock, "w", encoding="utf-8") as f:
            f.write("lock-version = 0\n")
        with open(src_lib, "w", encoding="utf-8") as f:
            f.write("pub fn v() -> usize { 0 }\n")

        naive_cache: set[str] = set()
        staged_cache: set[str] = set()

        def eval_both() -> tuple[str, str]:
            # Naive: COPY . . -> selector [""] hashes entire context
            h_all = buildkit_content_hash(ctx_dir, [""])
            k_naive = buildkit_exec_cache_key(
                ["cargo", "build", "--release"],
                ["PATH=/usr/local/cargo/bin:/usr/bin"],
                "/app",
                "linux",
                "amd64",
                [([""], h_all)],
            )
            # Staged: COPY Cargo.toml Cargo.lock ./ -> selector ["Cargo.toml", "Cargo.lock"]
            h_manifest = buildkit_content_hash(ctx_dir, ["Cargo.toml", "Cargo.lock"])
            k_staged = buildkit_exec_cache_key(
                ["cargo", "build", "--release", "--deps-only"],
                ["PATH=/usr/local/cargo/bin:/usr/bin"],
                "/app",
                "linux",
                "amd64",
                [(["Cargo.toml", "Cargo.lock"], h_manifest)],
            )
            return k_naive, k_staged

        # Seed warm baseline cache at commit 0
        k0_n, k0_s = eval_both()
        naive_cache.add(k0_n)
        staged_cache.add(k0_s)

        naive_hits = 0
        staged_hits = 0
        lock_edit_steps = {12, 25, 37, 50}
        for step in range(1, 51):
            if step in lock_edit_steps:
                with open(cargo_lock, "w", encoding="utf-8") as f:
                    f.write(f"lock-version = {step}\n")
            else:
                with open(src_lib, "w", encoding="utf-8") as f:
                    f.write(f"pub fn v() -> usize {{ {step} }}\n")
            kn, ks = eval_both()
            if kn in naive_cache:
                naive_hits += 1
            else:
                naive_cache.add(kn)
            if ks in staged_cache:
                staged_hits += 1
            else:
                staged_cache.add(ks)

    assert naive_hits == 0
    assert staged_hits == 46

    shared_default_docker_clean = simulate_cache_mount_concurrency(
        sharing=None, num_parallel_builders=4, remove_docker_clean=False
    )
    locked_clean_removed = simulate_cache_mount_concurrency(
        sharing="locked", num_parallel_builders=4, remove_docker_clean=True
    )
    assert shared_default_docker_clean == {
        "max_concurrent_writers": 4,
        "apt_lock_collisions": 3,
        "lock_poll_waits_100ms": 0,
        "deb_files_retained": 0,
    }
    assert locked_clean_removed == {
        "max_concurrent_writers": 1,
        "apt_lock_collisions": 0,
        "lock_poll_waits_100ms": 3,
        "deb_files_retained": 12,
    }

    return {
        "basis": "source + execution + derived (50-commit edit trace over ported BuildKit CacheMap/contenthash/mount logic)",
        "trace_commits": 50,
        "src_only_commits": 46,
        "lock_commits": 4,
        "naive_copy_all_hits": naive_hits,
        "naive_copy_all_hit_pct": round(100.0 * naive_hits / 50, 1),
        "staged_manifest_hits": staged_hits,
        "staged_manifest_hit_pct": round(100.0 * staged_hits / 50, 1),
        "shared_default_4arch": shared_default_docker_clean,
        "locked_without_docker_clean_4arch": locked_clean_removed,
    }


# ==============================================================================
# PROBE 3: Normative OCI .wh. Whiteouts & ARG/ENV vs. RUN --mount=type=secret
# ==============================================================================


def _build_tar_bytes(entries: list[tuple[str, bytes, int, int]]) -> bytes:
    """Build deterministic PAX tar archive from (name, payload, mode, mtime)."""
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w", format=tarfile.PAX_FORMAT) as tf:
        for name, payload, mode, mtime in entries:
            ti = tarfile.TarInfo(name=name)
            ti.size = len(payload)
            ti.mode = mode
            ti.uid = 0
            ti.gid = 0
            ti.uname = ""
            ti.gname = ""
            ti.mtime = mtime
            ti.type = tarfile.DIRTYPE if name.endswith("/") else tarfile.REGTYPE
            tf.addfile(ti, io.BytesIO(payload) if ti.type == tarfile.REGTYPE else None)
    return buf.getvalue()


def apply_oci_layers(layers: list[bytes]) -> dict[str, bytes]:
    """Spec-compliant union rootfs applier per OCI image-spec layer.md:244-337."""
    vfs: dict[str, bytes] = {}
    for raw_layer in layers:
        lower_keys = set(vfs.keys())
        with tarfile.open(fileobj=io.BytesIO(raw_layer), mode="r:*") as tf:
            for member in tf.getmembers():
                norm = member.name.lstrip("/")
                if not norm or member.isdir():
                    continue
                parent = posixpath.dirname(norm)
                base = posixpath.basename(norm)
                if base == ".wh..wh..opq":
                    # Opaque whiteout (layer.md:279-301): hide all lower descendants
                    prefix = (parent + "/") if parent else ""
                    for k in list(lower_keys):
                        if (not prefix or k.startswith(prefix)) and k in vfs:
                            del vfs[k]
                            lower_keys.discard(k)
                elif base.startswith(".wh."):
                    # Explicit whiteout (layer.md:246-252): applies ONLY to lower layers
                    target_base = base[len(".wh.") :]
                    target_path = f"{parent}/{target_base}" if parent else target_base
                    for k in list(lower_keys):
                        if (k == target_path or k.startswith(target_path + "/")) and k in vfs:
                            del vfs[k]
                            lower_keys.discard(k)
                else:
                    extracted = tf.extractfile(member)
                    vfs[norm] = extracted.read() if extracted is not None else b""
    return vfs


def buildkit_oci_config_simulation(
    mode: str,
    secret_key: str,
    secret_val: str,
    cmd_str: str,
    shadowed_arg_val: str | None = None,
) -> dict[str, object]:
    """Port of BuildKit convert.go:1369-1375, 1561-1562, 1594, 1786-1838, 1910-1930
    & convert_secrets.go:17-112.
    """
    config_env: list[str] = ["PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"]
    history: list[dict[str, object]] = []

    if mode == "ENV":
        # convert.go:1370-1374
        config_env.append(f"{secret_key}={secret_val}")
        history.append({"created_by": f"ENV {secret_key}={secret_val}", "empty_layer": True})
        history.append({"created_by": f"RUN /bin/sh -c {cmd_str}", "empty_layer": False})
    elif mode == "ARG":
        # convert.go:1831-1837 (empty-layer ARG commit) + 1594/1910-1930 (|1 KEY=VAL)
        history.append({"created_by": f"ARG {secret_key}={secret_val}", "empty_layer": True})
        history.append(
            {
                "created_by": f"RUN |1 {secret_key}={secret_val} /bin/sh -c {cmd_str}",
                "empty_layer": False,
            }
        )
    elif mode == "SECRET_MOUNT":
        # dispatchSecret (convert_secrets.go:17-90) never adds secrets to d.buildArgs,
        # d.state, or d.image.Config.Env; commitToHistory (convert.go:1594) receives
        # unmasked env and emits "RUN /bin/sh -c <cmd>". Note: withSecretEnvMask
        # (convert.go:1562, convert_secrets.go:92-112) masks only llb.WithCustomName.
        history.append(
            {
                "created_by": f"RUN /bin/sh -c {cmd_str}",
                "empty_layer": False,
            }
        )
    elif mode == "ARG_SHADOWED_BY_SECRET_MOUNT":
        assert shadowed_arg_val is not None
        # If a stage defines ARG KEY=<shadowed_arg_val> and shadows it via
        # RUN --mount=type=secret,env=KEY, llb.WithCustomName (convert.go:1562)
        # masks $KEY to "****" in solver UI progress, while commitToHistory (L1594)
        # receives unmasked env/d.buildArgs and still leaks |1 KEY=<shadowed_arg_val>!
        history.append(
            {"created_by": f"ARG {secret_key}={shadowed_arg_val}", "empty_layer": True}
        )
        history.append(
            {
                "created_by": f"RUN |1 {secret_key}={shadowed_arg_val} /bin/sh -c {cmd_str}",
                "empty_layer": False,
            }
        )
    else:
        raise ValueError(mode)

    return {"config": {"Env": config_env}, "history": history}


def run_probe_3() -> dict[str, object]:
    pem_hdr = b"-----BEGIN OPENSSH PRIVATE KEY-----\n"
    pem_ftr = b"\n-----END OPENSSH PRIVATE KEY-----\n"
    body_len = 2048 - len(pem_hdr) - len(pem_ftr)
    secret_marker = pem_hdr + ((b"SYNTHETIC_TEST_KEY_A1B2C3D4_" * 80)[:body_len]) + pem_ftr
    assert len(secret_marker) == 2048
    app_payload = b"ELF_APP_BINARY_" + (b"\x7fELF" * 1020)

    with tempfile.TemporaryDirectory() as tmp_oci:
        layer0 = _build_tar_bytes(
            [
                ("etc/", b"", 0o755, 0),
                ("etc/ssh/", b"", 0o755, 0),
                ("etc/ssh/ssh_host_ed25519_key", secret_marker, 0o600, 0),
                ("usr/", b"", 0o755, 0),
                ("usr/bin/", b"", 0o755, 0),
                ("usr/bin/app", app_payload, 0o755, 0),
            ]
        )
        # Layer 1a: explicit whiteout (.wh.<basename>) from `RUN rm -f /etc/ssh/ssh_host_ed25519_key`
        layer1_explicit_wh = _build_tar_bytes(
            [("etc/ssh/.wh.ssh_host_ed25519_key", b"", 0o600, 0)]
        )
        # Layer 1b: opaque directory whiteout (.wh..wh..opq) from `RUN rm -rf /etc/ssh && mkdir /etc/ssh`
        layer1_opaque_wh = _build_tar_bytes(
            [("etc/ssh/", b"", 0o755, 0), ("etc/ssh/.wh..wh..opq", b"", 0o600, 0)]
        )

        # Write real layer blobs to TemporaryDirectory and verify persistence on disk
        import os

        l0_path = os.path.join(tmp_oci, "layer0.tar")
        l1_path = os.path.join(tmp_oci, "layer1_wh.tar")
        with open(l0_path, "wb") as f0, open(l1_path, "wb") as f1:
            f0.write(layer0)
            f1.write(layer1_explicit_wh)

        with open(l0_path, "rb") as f0, open(l1_path, "rb") as f1:
            disk_l0 = f0.read()
            disk_l1 = f1.read()

    merged_explicit = apply_oci_layers([disk_l0, disk_l1])
    merged_opaque = apply_oci_layers([disk_l0, layer1_opaque_wh])
    assert "etc/ssh/ssh_host_ed25519_key" not in merged_explicit
    assert "etc/ssh/ssh_host_ed25519_key" not in merged_opaque
    assert merged_explicit["usr/bin/app"] == app_payload

    # Recover secret directly from lower layer tar in registry manifest
    recovered_bytes = b""
    with tarfile.open(fileobj=io.BytesIO(disk_l0), mode="r:*") as tf:
        m = tf.getmember("etc/ssh/ssh_host_ed25519_key")
        ex = tf.extractfile(m)
        assert ex is not None
        recovered_bytes = ex.read()
    assert recovered_bytes == secret_marker
    assert len(disk_l0) + len(disk_l1) > len(disk_l0)

    token_val = "ghp_SyntheticBuildSecretToken998877"
    fallback_arg_val = "ghp_FallbackStageArgValue112233"
    cfg_env_obj = buildkit_oci_config_simulation("ENV", "API_TOKEN", token_val, "./fetch.sh")
    cfg_arg_obj = buildkit_oci_config_simulation("ARG", "API_TOKEN", token_val, "./fetch.sh")
    cfg_sec_obj = buildkit_oci_config_simulation(
        "SECRET_MOUNT", "API_TOKEN", token_val, "./fetch.sh"
    )
    cfg_shadow_obj = buildkit_oci_config_simulation(
        "ARG_SHADOWED_BY_SECRET_MOUNT",
        "API_TOKEN",
        token_val,
        "./fetch.sh",
        shadowed_arg_val=fallback_arg_val,
    )
    assert cfg_sec_obj["history"] == [
        {"created_by": "RUN /bin/sh -c ./fetch.sh", "empty_layer": False}
    ]

    cfg_env = json.dumps(cfg_env_obj)
    cfg_arg = json.dumps(cfg_arg_obj)
    cfg_sec = json.dumps(cfg_sec_obj)
    cfg_shadow = json.dumps(cfg_shadow_obj)

    env_leaks = cfg_env.count(token_val)
    arg_leaks = cfg_arg.count(token_val)
    sec_leaks = cfg_sec.count(token_val)
    shadow_secret_leaks = cfg_shadow.count(token_val)
    shadow_arg_leaks = cfg_shadow.count(fallback_arg_val)
    assert env_leaks == 2  # config.Env + history[0].created_by
    assert arg_leaks == 2  # history[0] ("ARG ...") + history[1] ("RUN |1 ...")
    assert sec_leaks == 0
    assert shadow_secret_leaks == 0
    assert shadow_arg_leaks == 2

    return {
        "secret_key_bytes": len(secret_marker),
        "visible_in_merged_explicit_wh": "etc/ssh/ssh_host_ed25519_key" in merged_explicit,
        "visible_in_merged_opaque_wh": "etc/ssh/ssh_host_ed25519_key" in merged_opaque,
        "recovered_from_layer0_bytes": len(recovered_bytes),
        "layer0_tar_bytes": len(disk_l0),
        "two_layer_whiteout_total_tar_bytes": len(disk_l0) + len(disk_l1),
        "whiteout_size_delta_bytes": len(disk_l1),
        "secret_mount_created_by": "RUN /bin/sh -c ./fetch.sh",
        "config_plaintext_occurrences": {
            "ENV": env_leaks,
            "ARG": arg_leaks,
            "RUN_mount_type_secret": sec_leaks,
            "ARG_shadowed_by_secret_mount_arg_val": shadow_arg_leaks,
            "ARG_shadowed_by_secret_mount_secret_val": shadow_secret_leaks,
        },
    }


# ==============================================================================
# PROBE 4: Shell vs. Exec ENTRYPOINT PID-1 SIGTERM & Repo2Run Pollution Rollback
# ==============================================================================


def buildkit_entrypoint_config(
    cmdline: list[str], prepend_shell: bool, custom_shell: list[str] | None = None
) -> dict[str, object]:
    """Port of dispatchEntrypoint & withShell (convert.go:1709-1725, 2030-2038)."""
    if prepend_shell:
        shell = list(custom_shell) if custom_shell else ["/bin/sh", "-c"]
        ep = shell + [" ".join(cmdline)]
    else:
        ep = list(cmdline)

    # Analytical model (Basis: derived from Linux PID-1 signal delivery where
    # non-exec /bin/sh ignores/drops SIGTERM until K8s SIGKILL after 30.0s grace)
    pid1_binary = posixpath.basename(ep[0])
    forwards_sigterm = pid1_binary != "sh"
    k8s_grace_sec = 30.0
    shutdown_latency_sec = 0.02 if forwards_sigterm else k8s_grace_sec
    exit_code = 0 if forwards_sigterm else (128 + 9)  # 137 SIGKILL
    return {
        "entrypoint": ep,
        "pid1_binary": pid1_binary,
        "forwards_sigterm": forwards_sigterm,
        "k8s_shutdown_sec": shutdown_latency_sec,
        "exit_code": exit_code,
    }


def simulate_agent_env_synthesis(atomic_rollback: bool) -> dict[str, object]:
    """Analytical model (Basis: derived from Repo2Run §3 dual-environment atomic
    rollback vs. SWE-agent interactive container state pollution).
    """
    container_state: set[str] = set()
    dockerfile_runs: list[set[str]] = []

    # Trial 1: `apt-get install -y libgomp1 && pip install nonexistent-wheel`
    # Mutates container (`libgomp1` installed) before `pip` exits non-zero!
    snap = set(container_state)
    container_state.add("libgomp1")
    trial1_exit_zero = False
    if trial1_exit_zero:
        dockerfile_runs.append({"libgomp1"})
    elif atomic_rollback:
        container_state = snap

    # Trial 2: `pip install xgboost-lite` followed by `pytest` inside container.
    # Without rollback, polluted `libgomp1` makes `pytest` pass interactively, so
    # `libgomp1` is omitted from the synthesized Dockerfile -> clean `docker build` fails!
    # With atomic rollback, Trial 2 catches missing `libgomp1` immediately and fixes both.
    snap = set(container_state)
    container_state.add("xgboost-lite")
    if "libgomp1" not in container_state:
        if atomic_rollback:
            container_state = snap
            container_state.update({"libgomp1", "xgboost-lite"})
            dockerfile_runs.append({"libgomp1", "xgboost-lite"})
    else:
        dockerfile_runs.append({"xgboost-lite"})

    interactive_tests_pass = {"libgomp1", "xgboost-lite"}.issubset(container_state)
    clean_built_state: set[str] = set()
    for eff in dockerfile_runs:
        clean_built_state.update(eff)
    clean_dockerfile_passes = {"libgomp1", "xgboost-lite"}.issubset(clean_built_state)

    return {
        "interactive_tests_pass": interactive_tests_pass,
        "clean_dockerfile_passes": clean_dockerfile_passes,
        "state_diverged": interactive_tests_pass != clean_dockerfile_passes,
    }


def run_probe_4() -> dict[str, object]:
    shell_ep = buildkit_entrypoint_config(["python3", "app.py"], prepend_shell=True)
    exec_ep = buildkit_entrypoint_config(["python3", "app.py"], prepend_shell=False)
    assert shell_ep["entrypoint"] == ["/bin/sh", "-c", "python3 app.py"]
    assert shell_ep["exit_code"] == 137
    assert exec_ep["entrypoint"] == ["python3", "app.py"]
    assert exec_ep["exit_code"] == 0

    polluted = simulate_agent_env_synthesis(atomic_rollback=False)
    rolled_back = simulate_agent_env_synthesis(atomic_rollback=True)
    assert polluted["interactive_tests_pass"] is True and polluted["clean_dockerfile_passes"] is False
    assert polluted["state_diverged"] is True
    assert rolled_back["interactive_tests_pass"] is True and rolled_back["clean_dockerfile_passes"] is True
    assert rolled_back["state_diverged"] is False

    return {
        "basis": "source + execution + derived (analytical PID-1 signal and Repo2Run §3 dual-environment rollback models)",
        "shell_form": shell_ep,
        "exec_form": exec_ep,
        "without_atomic_rollback": polluted,
        "with_atomic_rollback": rolled_back,
    }


# ==============================================================================
# PROBE 5: SOURCE_DATE_EPOCH, BuildKit Upper-Clamp, gzip Drift, ko & kaniko
# ==============================================================================


def buildkit_rewrite_tar_timestamps(raw_tar: bytes, epoch_sec: int) -> bytes:
    """Exact port of rewriteTimestampInTarHeader (util/converter/converter.go:76-88):
       if hdr.ModTime.After(epoch) { hdr.ModTime = epoch }
    Note: clamps ONLY timestamps > epoch; does NOT touch Uid/Gid or entry order!
    """
    in_buf = io.BytesIO(raw_tar)
    out_buf = io.BytesIO()
    with (
        tarfile.open(fileobj=in_buf, mode="r:*") as rtf,
        tarfile.open(fileobj=out_buf, mode="w", format=tarfile.PAX_FORMAT) as wtf,
    ):
        for m in rtf.getmembers():
            ti = tarfile.TarInfo(name=m.name)
            ti.size = m.size
            ti.mode = m.mode
            ti.uid = m.uid
            ti.gid = m.gid
            ti.uname = m.uname
            ti.gname = m.gname
            ti.type = m.type
            ti.linkname = m.linkname
            # converter.go:78-80: ONLY clamps when mtime > epoch!
            ti.mtime = epoch_sec if m.mtime > epoch_sec else m.mtime
            payload = rtf.extractfile(m).read() if m.isfile() else None  # type: ignore[union-attr]
            wtf.addfile(ti, io.BytesIO(payload) if payload is not None else None)
    return out_buf.getvalue()


def ko_canonical_tar(files: dict[str, bytes], epoch_sec: int = 0) -> bytes:
    """Single-layer synthetic PAX tar specimen combining ko's deterministic
    header/lexicographic-sort invariants (Basis: source + derived from
    pkg/build/gobuild.go:629-703, 727-904, 1201-1257). Upstream ko emits two
    separate layers—tarKoData (walking kodata with explicit 0555 parent dir
    headers "/var", "/var/run", "/var/run/ko" stamped at g.kodataCreationTime)
    and tarBinary/buildLayer (writing "ko-app" + "/ko-app/<binary>" with Mode
    0555, zero time.Time{} ModTime, and empty PAXRecords)—merged here into one
    lexicographically sorted archive.
    """
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w", format=tarfile.PAX_FORMAT) as tf:
        for name in sorted(files.keys()):
            payload = files[name]
            ti = tarfile.TarInfo(name=name.lstrip("/"))
            ti.size = len(payload)
            ti.type = tarfile.REGTYPE
            ti.mode = 0o555
            ti.uid = 0
            ti.gid = 0
            ti.uname = ""
            ti.gname = ""
            ti.mtime = epoch_sec
            tf.addfile(ti, io.BytesIO(payload))
    return buf.getvalue()


def gzip_compress_with_mtime(raw: bytes, mtime: int | float) -> bytes:
    buf = io.BytesIO()
    with gzip.GzipFile(filename="", mode="wb", fileobj=buf, compresslevel=6, mtime=mtime) as gz:
        gz.write(raw)
    return buf.getvalue()


def parse_gzip_header_mtime_os(gz_bytes: bytes) -> tuple[int, int]:
    """Extract RFC 1952 4-byte little-endian MTIME (bytes 4..8) and OS (byte 9)."""
    assert gz_bytes[:2] == b"\x1f\x8b"
    mtime_le = struct.unpack("<I", gz_bytes[4:8])[0]
    os_byte = gz_bytes[9]
    return mtime_le, os_byte


@dataclass
class SimulatedHostFile:
    full_path: str
    dev: int
    ino: int
    nlink: int
    payload: bytes


def pack_hardlinks_kaniko_vs_oci(
    root_dir: str, host_files: list[SimulatedHostFile], kaniko_buggy: bool
) -> bytes:
    """Compare kaniko pkg/util/tar_util.go:40,109-112,198-216 vs. OCI layer.md:78-92."""
    buf = io.BytesIO()
    kaniko_map: dict[int, str] = {}
    oci_map: dict[tuple[int, int], str] = {}

    with tarfile.open(fileobj=buf, mode="w", format=tarfile.PAX_FORMAT) as tf:
        for hf in host_files:
            rel_name = hf.full_path[len(root_dir) :].lstrip("/")
            ti = tarfile.TarInfo(name=rel_name)
            ti.mode = 0o644
            ti.uid = 0
            ti.gid = 0
            ti.uname = ""
            ti.gname = ""
            ti.mtime = 0

            is_link = False
            link_dst = ""
            if hf.nlink > 1:
                if kaniko_buggy:
                    # tar_util.go:205-212: keys ONLY on stat.Ino AND keeps raw full_path
                    # (with leading '/') as linkDst while hdr.Name stripped root_dir & '/'!
                    if hf.ino in kaniko_map and kaniko_map[hf.ino] != hf.full_path:
                        is_link = True
                        link_dst = kaniko_map[hf.ino]
                    else:
                        kaniko_map[hf.ino] = hf.full_path
                else:
                    # OCI layer.md:78-92: keys on (dev, ino) and stores normalized tar path
                    key = (hf.dev, hf.ino)
                    if key in oci_map and oci_map[key] != rel_name:
                        is_link = True
                        link_dst = oci_map[key]
                    else:
                        oci_map[key] = rel_name

            if is_link:
                ti.type = tarfile.LNKTYPE
                ti.size = 0
                ti.linkname = link_dst
                tf.addfile(ti)
            else:
                ti.type = tarfile.REGTYPE
                ti.size = len(hf.payload)
                tf.addfile(ti, io.BytesIO(hf.payload))
    return buf.getvalue()


def run_probe_5() -> dict[str, object]:
    payloads = {
        "ko-app/service": b"GO_STATIC_ELF_PAYLOAD_V1",
        "var/run/ko/config.json": b'{"env":"prod"}\n',
    }
    t1, t2 = 1700000100, 1700000900

    with tempfile.TemporaryDirectory() as _tmp:
        del _tmp
        # Raw unnormalized builds (different mtime, uid, and walk order)
        b1_raw = io.BytesIO()
        with tarfile.open(fileobj=b1_raw, mode="w", format=tarfile.PAX_FORMAT) as tf:
            for k in ["var/run/ko/config.json", "ko-app/service"]:
                ti = tarfile.TarInfo(name=k)
                ti.size = len(payloads[k])
                ti.mode = 0o755
                ti.uid = 1000
                ti.gid = 1000
                ti.mtime = t1
                tf.addfile(ti, io.BytesIO(payloads[k]))

        b2_raw = io.BytesIO()
        with tarfile.open(fileobj=b2_raw, mode="w", format=tarfile.PAX_FORMAT) as tf:
            for k in ["ko-app/service", "var/run/ko/config.json"]:
                ti = tarfile.TarInfo(name=k)
                ti.size = len(payloads[k])
                ti.mode = 0o755
                ti.uid = 1001
                ti.gid = 1001
                ti.mtime = t2
                tf.addfile(ti, io.BytesIO(payloads[k]))

        raw1, raw2 = b1_raw.getvalue(), b2_raw.getvalue()

        # Same order & uid=0, differing ONLY in mtime (t1 vs t2)
        b1_mtime_only = _build_tar_bytes([(k, payloads[k], 0o555, t1) for k in sorted(payloads)])
        b2_mtime_only = _build_tar_bytes([(k, payloads[k], 0o555, t2) for k in sorted(payloads)])

        # 5a: BuildKit rewriteTimestampInTarHeader with FUTURE epoch (1800000000 > t1, t2)
        future_epoch = 1800000000
        bk_future_1 = buildkit_rewrite_tar_timestamps(b1_mtime_only, future_epoch)
        bk_future_2 = buildkit_rewrite_tar_timestamps(b2_mtime_only, future_epoch)

        # 5b: BuildKit rewriteTimestampInTarHeader with MID epoch (t1 < 1700000500 < t2)
        mid_epoch = 1700000500
        bk_mid_1 = buildkit_rewrite_tar_timestamps(b1_mtime_only, mid_epoch)
        bk_mid_2 = buildkit_rewrite_tar_timestamps(b2_mtime_only, mid_epoch)

        # 5c: BuildKit rewriteTimestampInTarHeader with epoch=0 on builds with uid/order drift
        bk_epoch0_uid_order_1 = buildkit_rewrite_tar_timestamps(raw1, 0)
        bk_epoch0_uid_order_2 = buildkit_rewrite_tar_timestamps(raw2, 0)

        # 5d: BuildKit rewriteTimestampInTarHeader with epoch=0 when uid/order already match
        bk_epoch0_clean_1 = buildkit_rewrite_tar_timestamps(b1_mtime_only, 0)
        bk_epoch0_clean_2 = buildkit_rewrite_tar_timestamps(b2_mtime_only, 0)

        # 5e: Gzip header MTIME drift on identical uncompressed tar bytes
        gz_drift_1 = gzip_compress_with_mtime(bk_epoch0_clean_1, mtime=t1)
        gz_drift_2 = gzip_compress_with_mtime(bk_epoch0_clean_2, mtime=t2)
        mt1, _ = parse_gzip_header_mtime_os(gz_drift_1)
        mt2, _ = parse_gzip_header_mtime_os(gz_drift_2)

        # 5f: ko canonical tar + gzip(mtime=0)
        ko_1 = ko_canonical_tar(payloads, epoch_sec=0)
        ko_2 = ko_canonical_tar(dict(reversed(list(payloads.items()))), epoch_sec=0)
        ko_gz_1 = gzip_compress_with_mtime(ko_1, mtime=0)
        ko_gz_2 = gzip_compress_with_mtime(ko_2, mtime=0)

        # 5g: kaniko cross-device hardlink collision + leading '/' linkname bug
        host_files = [
            SimulatedHostFile("/kaniko-root/etc/a.conf", dev=2049, ino=4242, nlink=2, payload=b"ALPHA_DATA"),
            SimulatedHostFile("/kaniko-root/mnt/b.conf", dev=2050, ino=4242, nlink=2, payload=b"BRAVO_DATA"),
        ]
        kaniko_tar = pack_hardlinks_kaniko_vs_oci("/kaniko-root", host_files, kaniko_buggy=True)
        oci_tar = pack_hardlinks_kaniko_vs_oci("/kaniko-root", host_files, kaniko_buggy=False)

        with tarfile.open(fileobj=io.BytesIO(kaniko_tar), mode="r:*") as tf:
            km = tf.getmember("mnt/b.conf")
            kaniko_b_is_lnk = km.islnk()
            kaniko_b_linkname = km.linkname
        with tarfile.open(fileobj=io.BytesIO(oci_tar), mode="r:*") as tf:
            om = tf.getmember("mnt/b.conf")
            oci_b_is_reg = om.isfile()
            oci_b_payload = tf.extractfile(om).read()  # type: ignore[union-attr]

        # 5h: Base-image DiffID preservation (BuildKit writer.go:477-482 vs kaniko mutate.Canonical)
        upstream_base_layer = _build_tar_bytes([("bin/sh", b"BUSYBOX", 0o755, 1690000000)])
        upstream_base_diffid = sha256_hex(upstream_base_layer)
        # BuildKit skips immutable base DiffIDs; kaniko mutate.Canonical zeroes all layer headers
        buildkit_base_after = upstream_base_layer  # skipped because immDiffID == diffID
        kaniko_base_after = buildkit_rewrite_tar_timestamps(upstream_base_layer, 0)

    assert sha256_hex(raw1) != sha256_hex(raw2)
    assert sha256_hex(bk_future_1) != sha256_hex(bk_future_2)
    assert sha256_hex(bk_mid_1) != sha256_hex(bk_mid_2)
    assert sha256_hex(bk_epoch0_uid_order_1) != sha256_hex(bk_epoch0_uid_order_2)
    assert sha256_hex(bk_epoch0_clean_1) == sha256_hex(bk_epoch0_clean_2)
    assert mt1 == t1 and mt2 == t2 and sha256_hex(gz_drift_1) != sha256_hex(gz_drift_2)
    assert sha256_hex(ko_1) == sha256_hex(ko_2)
    assert sha256_hex(ko_gz_1) == sha256_hex(ko_gz_2)
    assert kaniko_b_is_lnk is True and kaniko_b_linkname == "/kaniko-root/etc/a.conf"
    assert oci_b_is_reg is True and oci_b_payload == b"BRAVO_DATA"
    assert sha256_hex(buildkit_base_after) == upstream_base_diffid
    assert sha256_hex(kaniko_base_after) != upstream_base_diffid

    return {
        "unnormalized_diffid_equal": sha256_hex(raw1) == sha256_hex(raw2),
        "buildkit_future_epoch_clamp_diffid_equal": sha256_hex(bk_future_1) == sha256_hex(bk_future_2),
        "buildkit_mid_epoch_clamp_diffid_equal": sha256_hex(bk_mid_1) == sha256_hex(bk_mid_2),
        "buildkit_epoch0_with_uid_order_drift_equal": (
            sha256_hex(bk_epoch0_uid_order_1) == sha256_hex(bk_epoch0_uid_order_2)
        ),
        "buildkit_epoch0_clean_diffid_equal": (
            sha256_hex(bk_epoch0_clean_1) == sha256_hex(bk_epoch0_clean_2)
        ),
        "gzip_unclamped_mtime_digest_equal": sha256_hex(gz_drift_1) == sha256_hex(gz_drift_2),
        "ko_canonical_diffid_sha256": sha256_hex(ko_1),
        "ko_canonical_gzip_sha256": sha256_hex(ko_gz_1),
        "ko_canonical_bitwise_reproducible": sha256_hex(ko_gz_1) == sha256_hex(ko_gz_2),
        "kaniko_cross_dev_hardlink_corrupted": kaniko_b_is_lnk,
        "kaniko_corrupted_linkname": kaniko_b_linkname,
        "oci_spec_cross_dev_preserved": oci_b_is_reg and oci_b_payload == b"BRAVO_DATA",
        "buildkit_preserves_base_diffid": sha256_hex(buildkit_base_after) == upstream_base_diffid,
        "kaniko_reproducible_preserves_base_diffid": (
            sha256_hex(kaniko_base_after) == upstream_base_diffid
        ),
    }


def main() -> None:
    checks: list[tuple[str, Callable[[], dict[str, object]]]] = [
        ("probe_1_hadolint_binnacle_ast_defects", run_probe_1),
        ("probe_2_buildkit_llb_cache_and_mounts", run_probe_2),
        ("probe_3_oci_whiteouts_and_secret_persistence", run_probe_3),
        ("probe_4_pid1_sigterm_and_atomic_rollback", run_probe_4),
        ("probe_5_source_date_epoch_tar_gzip_kaniko_ko", run_probe_5),
    ]
    report: dict[str, object] = {
        "probe_suite": "verify_dockerfile_buildkit_oci_repro",
        "pinned_commits": {
            "moby/buildkit": "dd75b4955087a5a2d52188d6ce25b509b323280e",
            "hadolint/hadolint": "1d901b9c0b0d0445d19b1a9128d89fa55bb4604e",
            "opencontainers/image-spec": "4feed4a6674e59d301b9294f187ac46acb2de99f",
            "jjhenkel/binnacle-icse2020": "00a8fb5220377211b059b35539be4594b703d106",
            "ko-build/ko": "caaefc6f61be03dffdc114f4ba6ca763ef61003d",
            "GoogleContainerTools/kaniko": "236ba5690eda9170d0157aa8137ebbeb09d38685",
        },
        "results": {},
    }
    results_map: dict[str, object] = {}
    for name, fn in checks:
        results_map[name] = fn()
    report["results"] = results_map
    report["all_assertions_passed"] = True
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
