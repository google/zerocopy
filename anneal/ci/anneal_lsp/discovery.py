# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Workspace, toolchain, and zero-`.lake` artifact discovery for Lean 4."""

from __future__ import annotations

import contextlib
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import sys
import tempfile
from typing import Any


_DEFAULT_LOCKED_LEAN_SHA256 = (
    "79fb1d26fa5a39385d59fdc48a711a14b0710ca6480271acce99b4d177cea085",
    "1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554",
    "998f0cc2a5a754cc66df1f33b85e1447528737ff15012db35d8c501754b02f1e",
    "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",
)


def _load_locked_lean_sha256() -> frozenset[str]:
    lock_p = Path(__file__).resolve().parents[2] / "trusted/lean/foundation-lock.json"
    with contextlib.suppress(OSError, ValueError, UnicodeDecodeError):
        if lock_p.is_file() and not lock_p.is_symlink():
            data = json.loads(lock_p.read_text("utf-8"))
            dists = data.get("distributions") if isinstance(data, dict) else None
            if isinstance(dists, dict):
                digs = {v.lower() for v in dists.values() if isinstance(v, str) and len(v) == 64}
                if digs:
                    return frozenset(digs)
    return frozenset(_DEFAULT_LOCKED_LEAN_SHA256)


_LOCKED_LEAN_SHA256 = _load_locked_lean_sha256()


def _sha256_regular(path: Path) -> str | None:
    o_flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    try:
        fd = os.open(path, o_flags)
    except OSError:
        return None
    try:
        if not stat.S_ISREG(os.fstat(fd).st_mode):
            return None
        h = hashlib.sha256()
        with os.fdopen(fd, "rb") as fh:
            fd = -1
            while chunk := fh.read(1024 * 1024):
                h.update(chunk)
        return h.hexdigest()
    except OSError:
        return None
    finally:
        if fd >= 0:
            with contextlib.suppress(OSError):
                os.close(fd)


def _is_locked_lean(cand: Path) -> bool:
    for probe in (cand, _resolve_shim(cand)):
        if (dig := _sha256_regular(probe)) is not None and dig in _LOCKED_LEAN_SHA256:
            return True
    return False


def _load_pinned_toolchain() -> str:
    tc = Path(__file__).resolve().parents[2] / "trusted/lean/lean-toolchain"
    try:
        if tc.is_file() and not tc.is_symlink() and (txt := tc.read_text("utf-8").strip()):
            return txt
    except (OSError, UnicodeDecodeError):
        pass
    return "leanprover/lean4:v4.34.1"


PINNED_TOOLCHAIN = _load_pinned_toolchain()


@dataclass(frozen=True)
class WorkspaceContext:
    """Resolved Lean LSP launch environment for a `.lean` target."""

    mode: str
    root: Path
    lean_bin: Path | None
    lake_bin: Path | None
    lean_path: tuple[Path, ...]
    lean_src_path: tuple[Path, ...]
    artifacts_dir: Path | None
    unit_name: str | None
    watch_paths: tuple[Path, ...]
    needs_anneal_prebuilt: bool = False
    prebuilt_paths: tuple[Path, ...] = ()
    source_paths: tuple[Path, ...] = ()

    def fingerprint(self) -> tuple[Any, ...]:
        """Inode/mtime signature used to restart workers on artifact drift."""
        sig: list[Any] = [
            self.mode, str(self.root), str(self.lean_bin) if self.lean_bin else None,
            str(self.lake_bin) if self.lake_bin else None,
            tuple(str(p) for p in self.lean_path), tuple(str(p) for p in self.lean_src_path),
        ]
        for item in self.watch_paths:
            try:
                st = item.stat()
                sig.append((str(item), st.st_ino, st.st_mtime_ns, st.st_size))
            except OSError:
                sig.append((str(item), None))
        return tuple(sig)

    def missing_artifacts_hint(self) -> str | None:
        """Return setup guidance when an Anneal unit or tree lacks `.olean`s."""
        sys_lib = lean_sysroot_lib(self.lean_bin)
        non_sys = [p for p in self.lean_path if sys_lib is None or p != sys_lib]
        if self.mode == "anneal_unit":
            unit_lp = [p for p in non_sys if p not in self.prebuilt_paths]
            if any((p / "Expected.olean").is_file() or (p / "Captured.olean").is_file()
                   or any(p.glob("*.olean")) for p in unit_lp):
                return None
            if (req := self.root / "request.json").is_file():
                return (
                    f"No compiled `lean-lib/` found. Run `cargo anneal verify --request {req}"
                    " --artifacts <dir> --export-lean-lib` and pass `--artifacts <dir>`."
                )
            return "Pass `--artifacts <dir>` or set `ANNEAL_LSP_LEAN_PATH`."
        if self.mode == "lean_dir" and self.needs_anneal_prebuilt:
            names = ("Trusted.olean", "Trusted/MirAst.olean")
            if any((p / f).is_file() for p in non_sys for f in names):
                return None
            lb = str(self.lean_bin) if self.lean_bin else "<path/to/lean>"
            return (
                "No prebuilt Anneal `.olean`s found (`share/anneal/prebuilt` or "
                "`ANNEAL_LSP_LEAN_PATH`). Run `cargo anneal setup` or `python3 -I -B "
                f"anneal/ci/prebuild_bundled_oleans.py --lean-bin {lb} --output-dir <dir>` "
                "(then set `ANNEAL_LSP_LEAN_PATH=<dir>/lib`)."
            )
        return None


def _dedup_dirs(paths: list[Path]) -> tuple[Path, ...]:
    out, seen = [], set()
    for p in paths:
        try:
            if (rp := p.expanduser().resolve()).is_dir() and rp not in seen:
                seen.add(rp)
                out.append(rp)
        except OSError:
            pass
    return tuple(out)


def _safe_rel_path(base: Path, *parts: str) -> Path:
    """Join `parts` onto `base`, rejecting any symlinked path segment."""
    cur = base
    for part in parts:
        cur = cur / part
        if cur.is_symlink():
            raise PermissionError(f"Refusing symlinked workspace path: {cur}")
    return cur


def _default_home() -> Path | None:
    with contextlib.suppress(RuntimeError, OSError):
        return Path.home()
    return None


def _safe_roots(home: Path | None = None) -> tuple[Path, ...]:
    dh = home or _default_home()
    bases = (*( (dh,) if dh is not None else () ), Path(tempfile.gettempdir()), Path("/tmp"))
    roots: list[Path] = []
    for base in bases:
        exp = base.expanduser()
        roots.append(Path(os.path.abspath(str(exp))))
        with contextlib.suppress(OSError):
            roots.append(exp.resolve())
    return tuple(dict.fromkeys(roots))


def _reject_symlinks(
    raw_path: str | Path, *, home: Path | None = None, kind: str = "workspace target"
) -> Path:
    """Return lexical `abspath` after rejecting symlink targets and segments."""
    p0 = Path(raw_path).expanduser()
    abs_p = Path(os.path.abspath(str(p0)))
    roots = _safe_roots(home)
    if p0 not in roots and abs_p not in roots and (p0.is_symlink() or abs_p.is_symlink()):
        raise PermissionError(f"Refusing symlinked {kind}: {abs_p}")
    if ".." in p0.parts:
        step = Path(p0.anchor) if p0.is_absolute() else Path(os.path.abspath("."))
        for part in p0.parts:
            if part in (p0.anchor, "", "."):
                continue
            step = Path(os.path.abspath(str(step.parent))) if part == ".." else step / part
            if (
                step not in roots
                and not any(r.is_relative_to(step) for r in roots)
                and step.is_symlink()
            ):
                raise PermissionError(f"Refusing symlinked {kind}: {step}")
    for anc in (abs_p, *abs_p.parents):
        if anc in roots:
            break
        if anc.is_symlink():
            raise PermissionError(f"Refusing symlinked {kind}: {anc}")
    return abs_p


def validate_no_symlink_target(
    raw_path: str | Path, *, home: Path | None = None, kind: str = "workspace target"
) -> Path:
    """Resolve `raw_path` only after verifying no symlinked segments."""
    return _reject_symlinks(raw_path, home=home, kind=kind).resolve()


def _check_explicit_dir(
    raw: Path, *, home: Path | None = None, require_dir: bool = False
) -> Path:
    """Validate an explicit directory path without following symlinks inside roots."""
    checked = _reject_symlinks(raw, home=home, kind="artifact path")
    if require_dir:
        if not checked.exists():
            raise FileNotFoundError(f"Explicit artifacts directory not found: {checked}")
        if not checked.is_dir():
            raise NotADirectoryError(f"Explicit artifacts path is not a directory: {checked}")
    return checked


def _collect_artifact_files(dirs: tuple[Path, ...]) -> list[Path]:
    """Collect sorted non-symlink compiled Lean artifact files under `dirs`."""
    exts = (".olean", ".olean.private", ".olean.server", ".ilean", ".ir")
    out: list[Path] = []
    for d in dirs:
        if not d.is_dir():
            continue
        for cur, subdirs, files in os.walk(d, followlinks=False):
            subdirs[:] = [s for s in sorted(subdirs) if not (Path(cur) / s).is_symlink()]
            for fn in sorted(files):
                if fn.endswith(exts) and not (fp := Path(cur) / fn).is_symlink():
                    out.append(fp)
    return out


def _collect_source_files(dirs: tuple[Path, ...]) -> tuple[Path, ...]:
    """Collect sorted non-symlink `.lean` source files under `dirs`."""
    skip = frozenset({".git", ".lake", "target", "vendor", "__pycache__"})
    out: list[Path] = []
    seen: set[Path] = set()
    for d in dirs:
        if not d.is_dir():
            continue
        for cur, subdirs, files in os.walk(d, followlinks=False):
            subdirs[:] = [
                s for s in sorted(subdirs)
                if s not in skip and not (Path(cur) / s).is_symlink()
            ]
            for fn in sorted(files):
                if fn.endswith(".lean") and not (fp := Path(cur) / fn).is_symlink():
                    if (rfp := fp.resolve()) not in seen:
                        seen.add(rfp)
                        out.append(rfp)
    return tuple(out)


def _trusted_uids(start_dir: Path) -> set[int] | None:
    if not hasattr(os, "geteuid"):
        return None
    euid = os.geteuid()
    if euid != 0:
        return {euid}
    try:
        return {0, start_dir.lstat().st_uid}
    except OSError:
        return {0}


def _is_trusted_anc_dir(path: Path, allowed_uids: set[int] | None) -> bool:
    try:
        st = path.lstat()
    except OSError:
        return False
    if not stat.S_ISDIR(st.st_mode) or (st.st_mode & (stat.S_ISVTX | stat.S_IWOTH)):
        return False
    return allowed_uids is None or st.st_uid in allowed_uids


def _is_trusted_marker(path: Path, allowed_uids: set[int] | None) -> bool:
    try:
        st = path.lstat()
    except OSError:
        return False
    if not stat.S_ISREG(st.st_mode) or (st.st_mode & stat.S_IWOTH):
        return False
    return allowed_uids is None or st.st_uid in allowed_uids


def _read_tc(start: Path) -> tuple[str | None, bool]:
    cur = start if start.is_dir() else start.parent
    allowed_uids = _trusted_uids(cur)
    o_flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    for d in (cur, *cur.parents):
        if not _is_trusted_anc_dir(d, allowed_uids):
            break
        tc = d / "lean-toolchain"
        try:
            if tc.is_symlink():
                return None, True
            if tc.exists():
                if not _is_trusted_marker(tc, allowed_uids):
                    break
                fd = os.open(tc, o_flags)
                with os.fdopen(fd, "r", encoding="utf-8") as fh:
                    txt = fh.read(4096).strip()
                return (txt, False) if txt else (None, True)
        except (OSError, UnicodeDecodeError):
            return None, True
        if (d / ".git").exists():
            break
    return None, False


def is_elan_shim(cand: Path) -> bool:
    """Return True when `cand` is an `elan` or `elan-init` proxy binary."""
    try:
        if cand.resolve().name in ("elan", "elan-init"):
            return True
        elan = cand.parent / "elan"
        return elan.is_file() and cand.stat().st_ino == elan.stat().st_ino
    except OSError:
        return False


def _resolve_shim(cand: Path) -> Path:
    if is_elan_shim(cand):
        return Path(os.path.abspath(cand))
    return cand.resolve()


def find_lean_binary_optional(
    start: Path | None = None, explicit: Path | None = None, *,
    explicit_lake: Path | None = None, use_env: bool = True, home: Path | None = None,
) -> tuple[Path | None, Path | None]:
    """Locate `lean` and optional sibling `lake` without throwing if absent."""
    cands: list[Path] = []
    if explicit is not None:
        if not (exp := explicit.expanduser()).is_file():
            raise FileNotFoundError(f"Configured Lean binary not found: {exp}")
        cands.append(exp)
    if use_env:
        for var, tail in (("ANNEAL_LEAN", ""), ("ANNEAL_TEST_INSTALL_ROOT", "lean/bin/lean")):
            if raw := os.environ.get(var, "").strip():
                p = Path(raw).expanduser() / tail if tail else Path(raw).expanduser()
                if not p.is_file():
                    raise FileNotFoundError(f"Configured {var} missing lean: {p}")
                cands.append(p)
    override, raw_home = bool(cands), (home or _default_home())
    home_dir = raw_home.expanduser() if raw_home is not None else None
    tc, invalid_tc = _read_tc(start) if start else (None, False)
    if invalid_tc and not override:
        return None, None
    non_pinned = False
    if tc and tc != PINNED_TOOLCHAIN and not override:
        if home_dir is None or any(c.isspace() or ord(c) < 32 for c in tc) or any(
            seg in ("", ".", "..") for seg in tc.replace("\\", "/").split("/")
        ):
            return None, None
        er = home_dir / ".elan/toolchains"
        td = er / tc.replace("/", "--").replace(":", "---")
        try:
            ok_tc = er.is_dir() and td.resolve().is_relative_to(er.resolve())
        except OSError:
            ok_tc = False
        if not ok_tc or not (tc_cand := td / "bin/lean").is_file():
            return None, None
        cands.append(tc_cand)
        non_pinned = True
    elif not override:
        cache_dirs: list[Path] = []
        if sys.platform == "darwin":
            if home_dir is not None:
                cache_dirs.append(home_dir / "Library/Caches")
        else:
            xdg = os.environ.get("XDG_CACHE_HOME", "").strip() if use_env else ""
            xp = Path(xdg).expanduser() if xdg else None
            if xp and xp.is_absolute():
                cache_dirs.append(xp)
            elif home_dir is not None:
                cache_dirs.append(home_dir / ".cache")
        if home_dir is not None:
            cache_dirs.append(home_dir / "anneal")
        auto_cands: list[Path] = []
        for base_dir in cache_dirs:
            tc_cache = base_dir / ("toolchain" if base_dir.name == "anneal" else "anneal/toolchain")
            cached: list[tuple[float, Path]] = []
            try:
                for e in (tc_cache.iterdir() if tc_cache.is_dir() else ()):
                    if (cand := e / "lean/bin/lean").is_file():
                        cached.append((cand.stat().st_mtime, cand))
            except OSError:
                pass
            auto_cands.extend(p for _, p in sorted(cached, key=lambda x: x[0], reverse=True))
        if home_dir is not None:
            slug = PINNED_TOOLCHAIN.replace("/", "--").replace(":", "---")
            auto_cands.append(home_dir / ".elan/toolchains" / slug / "bin/lean")
        existing = [c for c in auto_cands if c.is_file()]
        cands.extend(c for c in existing if _is_locked_lean(c))
        cands.extend(existing)
        if use_env and (found := shutil.which("lean")):
            cands.append(Path(found))
    chosen = next(((c, _resolve_shim(c)) for c in cands if c.is_file()), None)
    if chosen is None:
        return None, None
    raw_cand, lean_bin = chosen
    if explicit_lake is not None:
        if not (exp_lake := explicit_lake.expanduser()).is_file():
            raise FileNotFoundError(f"Configured Lake binary not found: {exp_lake}")
        return lean_bin, _resolve_shim(exp_lake)
    for cand_dir in (lean_bin.parent, raw_cand.parent):
        if (sib := cand_dir / "lake").is_file():
            return lean_bin, _resolve_shim(sib)
    if use_env and not override and not non_pinned and (w := shutil.which("lake")):
        return lean_bin, _resolve_shim(Path(w))
    return lean_bin, None


def find_lean_binary(
    start: Path | None = None, explicit: Path | None = None, *,
    explicit_lake: Path | None = None, use_env: bool = True, home: Path | None = None,
) -> tuple[Path, Path | None]:
    """Locate `lean` and optional sibling `lake`, raising if unavailable."""
    lean_bin, lake_bin = find_lean_binary_optional(
        start, explicit, explicit_lake=explicit_lake, use_env=use_env, home=home,
    )
    if lean_bin is None:
        tc, invalid = _read_tc(start) if start else (None, False)
        kind = (
            "Invalid or unreadable `lean-toolchain` near"
            if invalid else "Unable to locate `lean` for"
        )
        tgt = start if invalid else (tc or PINNED_TOOLCHAIN)
        raise FileNotFoundError(f"{kind} `{tgt}`; set `ANNEAL_LEAN`.")
    return lean_bin, lake_bin


def lean_sysroot_lib(lean_bin: Path | None) -> Path | None:
    """Resolve Lean sysroot `lib/lean` statically without running binaries."""
    if lean_bin is None:
        return None
    for base in (lean_bin.parent.parent, lean_bin.resolve().parent.parent):
        if (lib := base / "lib/lean").is_dir():
            return lib.resolve()
    return None


def _has_safe_oleans(d: Path) -> bool:
    found = False
    for p in d.glob("*.olean"):
        if p.is_symlink():
            raise PermissionError(f"Refusing symlinked workspace path: {p}")
        found = True
    return found


def discover_workspace(
    file_path: str | Path, *, artifacts_dir: Path | None = None,
    extra_lean_path: list[Path] | None = None, extra_lean_src_path: list[Path] | None = None,
    explicit_lean: Path | None = None, explicit_lake: Path | None = None,
    cargo_target_dir: Path | None = None, test_install_root: Path | None = None,
    require_lean: bool = False, use_env: bool = True, home: Path | None = None,
) -> WorkspaceContext:
    """Resolve workspace mode, root, `LEAN_PATH`, and `LEAN_SRC_PATH`."""
    target = validate_no_symlink_target(file_path, home=home, kind="workspace target")
    start_dir = target if target.is_dir() else target.parent
    allowed_uids = _trusted_uids(start_dir)
    mode, root, unit_name, lake_lib, watch = "lean_dir", start_dir, None, None, []
    for anc in (start_dir, *start_dir.parents):
        if not _is_trusted_anc_dir(anc, allowed_uids):
            break
        if _is_trusted_marker(req := _safe_rel_path(anc, "request.json"), allowed_uids):
            mode, root, unit_name = "anneal_unit", anc, anc.name
            watch.append(req)
            break
        if any(
            _is_trusted_marker(_safe_rel_path(anc, lf), allowed_uids)
            for lf in ("lakefile.toml", "lakefile.lean")
        ):
            mode, root = "lake", anc
            lake_lib = _safe_rel_path(anc, ".lake", "build", "lib", "lean")
            lake_man = _safe_rel_path(anc, "lake-manifest.json")
            watch.extend([anc / "lakefile.toml", anc / "lakefile.lean", lake_man, lake_lib])
            break
        if (anc / ".git").exists():
            root = anc
            break

    lean_bin, lake_bin = (find_lean_binary if require_lean else find_lean_binary_optional)(
        start_dir, explicit=explicit_lean, explicit_lake=explicit_lake,
        use_env=use_env, home=home,
    )
    art_cands: list[Path] = []
    if artifacts_dir is not None:
        art_cands.append(_check_explicit_dir(artifacts_dir, home=home, require_dir=True))
    elif use_env and (ea := os.environ.get("ANNEAL_LSP_ARTIFACTS", "").strip()):
        art_cands.append(_check_explicit_dir(Path(ea), home=home, require_dir=True))
    if _is_trusted_anc_dir(root, allowed_uids):
        art_cands.extend([_safe_rel_path(root, "artifacts"), root])
    ct_raw = (str(cargo_target_dir) if cargo_target_dir is not None
              else (os.environ.get("CARGO_TARGET_DIR", "").strip() if use_env else ""))
    if unit_name:
        if ct_raw:
            ct = _check_explicit_dir(Path(ct_raw), home=home)
            art_cands.extend([
                _safe_rel_path(ct, "anneal-artifacts", unit_name),
                _safe_rel_path(ct, "anneal", unit_name),
            ])
        for anc in root.parents:
            if not _is_trusted_anc_dir(anc, allowed_uids):
                break
            for parts in (
                ("target", "anneal-artifacts"), ("target", "anneal"),
                ("anneal", "target", "anneal-artifacts"),
            ):
                art_cands.append(_safe_rel_path(anc, *parts, unit_name))
            if (anc / ".git").exists():
                break

    art_dir, lp, lsp = None, list(extra_lean_path or []), [root, *(extra_lean_src_path or [])]
    if use_env:
        for var, dst in (("ANNEAL_LSP_LEAN_PATH", lp), ("LEAN_PATH", lp), ("LEAN_SRC_PATH", lsp)):
            vals = os.environ.get(var, "").split(os.pathsep)
            dst.extend(Path(x.strip()) for x in vals if x.strip())
    for cand in art_cands:
        ll = _safe_rel_path(cand, "lean-lib")
        if ll.is_dir():
            art_dir = art_dir or cand.resolve()
            lp.append(ll)
        elif cand.is_dir() and _has_safe_oleans(cand):
            lp.append(cand)
        for sub in ("capture", "generated"):
            sp = _safe_rel_path(cand, sub)
            if sp.is_dir():
                lsp.append(sp)
    if art_dir:
        watch.extend(art_dir / s for s in ("lean-lib", "capture", "generated"))

    prebuilt: list[Path] = []
    if lean_bin and lean_bin.parent.name == "bin" and lean_bin.parent.parent.name == "lean":
        prebuilt.append(lean_bin.parent.parent.parent / "share/anneal/prebuilt")
    ir_raw = (
        str(test_install_root) if test_install_root is not None
        else (os.environ.get("ANNEAL_TEST_INSTALL_ROOT", "").strip() if use_env else "")
    )
    if ir_raw:
        prebuilt.append(Path(ir_raw).expanduser() / "share/anneal/prebuilt")
    needs_prebuilt = False
    for anc in (start_dir, *start_dir.parents):
        if not _is_trusted_anc_dir(anc, allowed_uids):
            break
        tl = _safe_rel_path(anc, "trusted", "lean", "Trusted.lean")
        atl = _safe_rel_path(anc, "anneal", "trusted", "lean", "Trusted.lean")
        ar = anc if tl.is_file() else (_safe_rel_path(anc, "anneal") if atl.is_file() else None)
        if ar is not None:
            for parts in (
                ("theory",), ("trusted", "lean"), ("correspondence",), ("trusted", "audit"),
            ):
                sp = _safe_rel_path(ar, *parts)
                if sp.is_dir():
                    lsp.append(sp)
            needs_prebuilt = any(
                (start_dir == (rs := sp.resolve()) or start_dir.is_relative_to(rs))
                for pts in (
                    ("theory",), ("correspondence",), ("trusted", "lean", "Trusted"),
                    ("trusted", "audit"),
                )
                if (sp := _safe_rel_path(ar, *pts)).exists()
            )
            break
        if (anc / ".git").exists():
            break
    pb_dirs: list[Path] = []
    for pb in (*prebuilt, Path("/opt/anneal-bundle/share/anneal/prebuilt")):
        if pb.is_dir():
            for d in (pb / "lib", pb):
                if d.is_dir():
                    lp.append(d)
                    pb_dirs.append(d)
            watch.append(pb)
    sys_lib = lean_sysroot_lib(lean_bin)
    non_sys_lp = _dedup_dirs(lp)
    if sys_lib is not None:
        lp.append(sys_lib)
    watch_art = tuple(
        d for d in (*non_sys_lp, *((lake_lib.resolve(),) if lake_lib and lake_lib.is_dir() else ()))
        if d != sys_lib
    )
    watch.extend(_collect_artifact_files(watch_art))
    for p in (start_dir / "lean-toolchain", root / "lean-toolchain"):
        if p.is_symlink():
            raise PermissionError(f"Refusing symlinked workspace path: {p}")
        if p.is_file():
            watch.append(p)
    dedup_lsp = _dedup_dirs(lsp)
    return WorkspaceContext(
        mode=mode, root=root, lean_bin=lean_bin, lake_bin=lake_bin,
        lean_path=_dedup_dirs(lp), lean_src_path=dedup_lsp,
        artifacts_dir=art_dir, unit_name=unit_name, watch_paths=tuple(dict.fromkeys(watch)),
        needs_anneal_prebuilt=needs_prebuilt, prebuilt_paths=_dedup_dirs(pb_dirs),
        source_paths=_collect_source_files(dedup_lsp),
    )
