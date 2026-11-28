#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Resolve merge conflicts in the SHA-256 pin manifests.

`trusted/root-manifest.sha256` and the `sha256` fields of
`theory/bundle-manifest.json` are derived from the files they pin, but which
files they pin is a reviewed decision. Run this after resolving every pinned
input; never hand-edit a digest.

With no arguments, resolve each manifest that has conflict markers. Each
side's membership is kept when the sides agree, and merged only when every
hunk has a base section (`merge.conflictStyle=diff3` or `zdiff3`) so each
side's additions and removals are known. Every digest is then recomputed
from the working tree. Any ambiguity, including differences outside the
entries, fails closed and leaves both manifests untouched.

When a conflict fails closed, resolve the membership by hand (remove the
markers, keeping any digest), then name the manifest (`root` or `bundle`):
a named manifest's membership is kept as written and only its digests are
recomputed. CI remains the authority on whether the result is consistent.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import sys
import tempfile

_CI_DIR = Path(__file__).resolve().parent
# `python3 -I` omits the script's directory from `sys.path`.
if str(_CI_DIR) not in sys.path:
    sys.path.insert(0, str(_CI_DIR))

import update_root_manifest  # noqa: E402

ROOT_MANIFEST = "trusted/root-manifest.sha256"
BUNDLE_MANIFEST = "theory/bundle-manifest.json"
TARGETS = {"root": ROOT_MANIFEST, "bundle": BUNDLE_MANIFEST}
# Mirrors `REQUIRED_THEORY_BUNDLE_PATH` in `trusted/cargo-anneal`.
REQUIRED_THEORY_MODULE = "theory/Anneal/MirWp.lean"
PLACEHOLDER_DIGEST = b"0" * 64
# Root-manifest comment and blank lines, as `ci/update_root_manifest.py`
# accepts them.
ROOT_OTHER_RE = re.compile(rb"#[^\r\n]*(?:\r?\n)?|(?:\r?\n)?")
# Every line that the canonical bundle-manifest serialization can contain.
BUNDLE_LINE_RE = re.compile(
    rb'(?:[{}]|  "schema_version": 1,|  "modules": \[\]?|  \]|    \{|    \},?'
    rb'|      "path": "(?P<path>[^"\\\r\n]*)",|      "sha256": "[0-9a-f]{64}")\n')
ENTRY_RE = re.compile(rb"[0-9a-f]{64}( [ *][^\r\n]+(?:\r?\n)?)")
LEAN_IDENT_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*")


class ResolveError(Exception):
    """The conflict needs a human decision or an input is not ready."""


def _marker(line):
    """Classify `line` as a Git conflict marker of the default size."""
    body = line.rstrip(b"\r\n")
    if body == b"=======":
        return "="
    for prefix, kind in ((b"<<<<<<<", "<"), (b"|||||||", "|"), (b">>>>>>>", ">")):
        if body == prefix or body.startswith(prefix + b" "):
            return kind
    return None


def has_conflict_markers(data, kinds="<|>"):
    """Report whether `data` has a conflict marker line of one of `kinds`.

    The default omits a bare `=======`, which ordinary pinned sources can
    contain; a real conflict always has an opening and closing marker.
    """
    return any((_marker(line) or "_") in kinds for line in data.splitlines())


def split_conflict(data):
    """Split conflicted bytes into `(ours, base, theirs)` file versions.

    Accept 2-way markers and the base sections of `merge.conflictStyle=diff3`
    and `zdiff3`. `base` is `None` unless every hunk carries a base section,
    because a partial base cannot show what either side changed. Otherwise it
    is a list of `(line, in_base_section)` pairs.

    `zdiff3` moves lines common to both sides out of a hunk, so lines outside
    the base sections can be absent from the true base. Callers read only
    membership from the base and prefer a base section's copy of an entry.
    An extra entry outside the base sections is harmless: every such line is
    in both ours and theirs, and an entry both sides keep survives the merge.
    """
    versions = {"<": [], "|": [], "=": []}
    base = []
    state = None
    hunks = 0
    hunks_with_base = 0
    for number, line in enumerate(data.splitlines(keepends=True), 1):
        kind = _marker(line)
        if kind is None:
            if state is None:
                for version in versions.values():
                    version.append(line)
                base.append((line, False))
            else:
                versions[state].append(line)
                if state == "|":
                    base.append((line, True))
        elif kind == "<" and state is None:
            state = "<"
            hunks += 1
        elif kind == "|" and state == "<":
            state = "|"
            hunks_with_base += 1
        elif kind == "=" and state in ("<", "|"):
            state = "="
        elif kind == ">" and state == "=":
            state = None
        else:
            raise ResolveError(f"line {number}: unexpected conflict marker")
    if state is not None:
        raise ResolveError("unterminated conflict hunk")
    if hunks_with_base != hunks:
        base = None
    return b"".join(versions["<"]), base, b"".join(versions["="])


def _checked_input(root, name):
    """Return the bytes of pinned input `name` once it is safe to hash."""
    path = PurePosixPath(name)
    if path.is_absolute() or not path.parts or ".." in path.parts or str(path) != name:
        raise ResolveError(f"{name}: expected a canonical relative path")
    if name in TARGETS.values():
        raise ResolveError(f"{name}: a pin manifest cannot pin itself")
    current = root
    # Inspect every component without following symlinks so a symlinked
    # directory cannot redirect a pin, even to a file inside the root.
    for index, part in enumerate(path.parts):
        current = current / part
        try:
            mode = os.lstat(current).st_mode
        except FileNotFoundError:
            raise ResolveError(f"{name}: missing pinned input") from None
        last = index == len(path.parts) - 1
        if stat.S_ISLNK(mode) or not (stat.S_ISREG(mode) if last else stat.S_ISDIR(mode)):
            raise ResolveError(f"{name}: expected a regular file without symlinks")
    data = current.read_bytes()
    if has_conflict_markers(data):
        raise ResolveError(f"{name}: resolve this input's conflict first")
    return data


def _git(root, *arguments):
    # Inherited `GIT_*` variables (such as `GIT_DIR` from a hook) could point
    # at another repository, and literal pathspecs keep a pinned name such as
    # `*.toml` from matching other files.
    environment = {key: value for key, value in os.environ.items()
                   if not key.startswith("GIT_")}
    return subprocess.run(["git", "--literal-pathspecs", "-c", "core.hooksPath=/dev/null",
                           "-C", str(root), *arguments],
                          env=environment, capture_output=True, check=False)


def unmerged_paths(root, names):
    """Return which of `names` Git records as unmerged.

    A modify/delete or binary conflict leaves no markers in the working tree,
    so the index is the only record. Outside a Git work tree there is nothing
    to consult.
    """
    try:
        inside = _git(root, "rev-parse", "--is-inside-work-tree")
    except FileNotFoundError:
        return []
    if inside.returncode != 0 and b"not a git repository" in inside.stderr:
        return []
    if inside.returncode != 0 or inside.stdout.strip() != b"true":
        raise ResolveError("cannot inspect the Git work tree: "
                           + inside.stderr.decode(errors="replace").strip())
    unmerged = _git(root, "ls-files", "--unmerged", "-z", "--", *names)
    if unmerged.returncode != 0:
        raise ResolveError("cannot read the Git index: "
                           + unmerged.stderr.decode(errors="replace").strip())
    return sorted({record.split(b"\t", 1)[1].decode(errors="replace")
                   for record in unmerged.stdout.split(b"\0") if b"\t" in record})


def _check_index(root, names):
    paths = unmerged_paths(root, names)
    if paths:
        raise ResolveError("unmerged pinned inputs: " + ", ".join(paths))


def _base_members(members, manifest):
    """Deduplicate `(key, value, in_base_section)` base members in order.

    Prefer a base section's copy; see `split_conflict` for why a duplicate
    outside the base sections is a `zdiff3` artifact.
    """
    chosen = {}
    for index, (key, value, in_section) in enumerate(members):
        if key in chosen:
            previous = members[chosen[key]][2]
            if previous == in_section:
                raise ResolveError(f"{manifest}: base lists {key} twice")
            if not in_section:
                continue
        chosen[key] = index
    return [members[index][:2] for index in sorted(chosen.values())]


def _merge_sets(ours, base, theirs):
    """Apply both sides' additions and removals relative to `base`."""
    return (ours & theirs) | ((ours | theirs) - base)


def _root_lines(data):
    """Parse root-manifest bytes into entry and verbatim lines."""
    items = []
    names = set()
    for line in data.splitlines(keepends=True):
        match = ENTRY_RE.fullmatch(line)
        if match is None:
            items.append(("line", line))
            continue
        tail = match[1]
        name = tail[2:].rstrip(b"\r\n").decode("utf-8")
        if name in names:
            raise ResolveError(f"{ROOT_MANIFEST}: duplicate entry {name}")
        names.add(name)
        items.append(("entry", name, tail))
    return items


def _entry_block(items, side):
    """Split parsed lines into `(prefix, entries, suffix)` around one block."""
    kinds = "".join("e" if item[0] == "entry" else "l" for item in items)
    if not re.fullmatch("l*e+l*", kinds):
        raise ResolveError(f"{ROOT_MANIFEST}: {side} entries are not one "
                           "contiguous block; resolve by hand")
    start, end = kinds.index("e"), kinds.rindex("e") + 1
    entries = [(name, tail) for _, name, tail in items[start:end]]
    if any(not tail.endswith(b"\n") for _, tail in entries):
        raise ResolveError(f"{ROOT_MANIFEST}: {side} has an unterminated entry")
    return items[:start], entries, items[end:]


def _root_base_entries(base):
    """Return the ordered `(name, tail)` entries of a reconstructed base.

    Fail closed on any line the updater would reject: skipping one would
    drop an entry from the base and turn a side's removal into an addition.
    """
    members = []
    for line, in_section in base:
        match = ENTRY_RE.fullmatch(line)
        if match is not None:
            members.append((match[1][2:].rstrip(b"\r\n").decode("utf-8"), match[1],
                            in_section))
        elif not ROOT_OTHER_RE.fullmatch(line):
            raise ResolveError(f"{ROOT_MANIFEST}: malformed base line; resolve by hand")
    return _base_members(members, ROOT_MANIFEST)


def _merge_root_order(ours, base, theirs):
    """Merge ordered entry lists, keeping each side's insertion points.

    Each addition stays after the nearest base entry that precedes it on its
    side. Where both sides add in the same gap, our additions come first:
    during a rebase, ours is the branch that already landed.
    """
    base_names = [name for name, _ in base]
    base_index = {name: index for index, name in enumerate(base_names)}
    sides = {"ours": ours, "theirs": theirs}
    gaps = {"ours": {}, "theirs": {}}
    for side, entries in sides.items():
        kept = [name for name, _ in entries if name in base_index]
        if kept != [name for name in base_names if name in kept]:
            raise ResolveError(f"{ROOT_MANIFEST}: {side} reorders base entries; "
                               "resolve by hand")
        gap = -1
        for name, tail in entries:
            if name in base_index:
                gap = base_index[name]
            else:
                gaps[side].setdefault(gap, []).append((name, tail))
    tails = {}
    for entries in (ours, theirs):
        for name, tail in entries:
            if tails.setdefault(name, tail) != tail:
                raise ResolveError(f"{ROOT_MANIFEST}: sides disagree on the "
                                   f"checksum mode of {name}")
    added = {}
    for side in sides:
        for gap, entries in gaps[side].items():
            for name, _ in entries:
                if added.setdefault(name, gap) != gap:
                    raise ResolveError(f"{ROOT_MANIFEST}: sides add {name} at "
                                       "different positions; resolve by hand")
    keep = _merge_sets({name for name, _ in ours}, set(base_names),
                       {name for name, _ in theirs})
    merged = []
    for gap in range(-1, len(base_names)):
        if gap >= 0 and base_names[gap] in keep:
            merged.append(base_names[gap])
        for side in sides:
            for name, _ in gaps[side].get(gap, []):
                if name not in merged:
                    merged.append(name)
    return [(name, tails[name]) for name in merged]


def resolve_root_manifest(root, data):
    """Return the resolved bytes of a conflicted root manifest."""
    ours_bytes, base_bytes, theirs_bytes = split_conflict(data)
    ours, theirs = _root_lines(ours_bytes), _root_lines(theirs_bytes)

    def skeleton(items):
        return [item[1:] if item[0] == "line" else item[2] for item in items]

    def names(items):
        return [item[1] for item in items if item[0] == "entry"]

    if names(ours) == names(theirs):
        if skeleton(ours) != skeleton(theirs):
            raise ResolveError(f"{ROOT_MANIFEST}: sides differ outside the "
                               "digests; resolve by hand")
        merged = [item[1] if item[0] == "line" else PLACEHOLDER_DIGEST + item[2]
                  for item in ours]
    else:
        if base_bytes is None:
            raise ResolveError(f"{ROOT_MANIFEST}: sides pin different files and "
                               "there is no base section (use "
                               "merge.conflictStyle=diff3); resolve by hand")
        ours_prefix, ours_entries, ours_suffix = _entry_block(ours, "ours")
        theirs_prefix, theirs_entries, theirs_suffix = _entry_block(theirs, "theirs")
        base_entries = _root_base_entries(base_bytes)
        if (ours_prefix, ours_suffix) != (theirs_prefix, theirs_suffix):
            raise ResolveError(f"{ROOT_MANIFEST}: sides differ outside the "
                               "entries; resolve by hand")
        entries = _merge_root_order(ours_entries, base_entries, theirs_entries)
        if not entries:
            raise ResolveError(f"{ROOT_MANIFEST}: merge removes every entry")
        merged = ([line for _, line in ours_prefix]
                  + [PLACEHOLDER_DIGEST + tail for _, tail in entries]
                  + [line for _, line in ours_suffix])
    names_to_hash = [item[1] for item in _root_lines(b"".join(merged))
                     if item[0] == "entry"]
    for name in names_to_hash:
        _checked_input(root, name)
    _check_index(root, names_to_hash)
    # Delegate hashing to the explicit updater so both tools share one entry
    # grammar and one set of input checks.
    with tempfile.TemporaryDirectory(prefix="anneal-pin-resolve-") as directory:
        staged = Path(directory) / "root-manifest.sha256"
        staged.write_bytes(b"".join(merged))
        try:
            return update_root_manifest.refreshed_manifest(root, staged)
        except update_root_manifest.ManifestError as error:
            raise ResolveError(f"{ROOT_MANIFEST}: {error}") from None


def _render_bundle(paths, digests):
    manifest = {"schema_version": 1,
                "modules": [{"path": path, "sha256": digests[path]} for path in paths]}
    return json.dumps(manifest, indent=2) + "\n"


def _no_duplicate_keys(pairs):
    keys = [key for key, _ in pairs]
    if len(keys) != len(set(keys)):
        raise ResolveError(f"{BUNDLE_MANIFEST}: duplicate JSON key")
    return dict(pairs)


def _bundle_paths(data, side):
    """Return the module paths of one canonically formatted manifest side."""
    try:
        text = data.decode("utf-8")
        manifest = json.loads(text, object_pairs_hook=_no_duplicate_keys)
    except (UnicodeError, ValueError) as error:
        raise ResolveError(f"{BUNDLE_MANIFEST}: {side} is not JSON: {error}") from None
    if (not isinstance(manifest, dict) or list(manifest) != ["schema_version", "modules"]
            or type(manifest["schema_version"]) is not int
            or manifest["schema_version"] != 1
            or not isinstance(manifest["modules"], list)):
        raise ResolveError(f"{BUNDLE_MANIFEST}: {side} differs from schema "
                           "version 1; resolve by hand")
    paths = []
    digests = {}
    for module in manifest["modules"]:
        if (not isinstance(module, dict) or list(module) != ["path", "sha256"]
                or not all(isinstance(value, str) for value in module.values())):
            raise ResolveError(f"{BUNDLE_MANIFEST}: {side} has a malformed "
                               "module entry; resolve by hand")
        paths.append(module["path"])
        digests[module["path"]] = module["sha256"]
    if len(set(paths)) != len(paths):
        raise ResolveError(f"{BUNDLE_MANIFEST}: {side} lists a module twice")
    # The loader requires sorted paths, and the manifest is serialized as
    # pretty JSON. Anything else is a non-entry difference for a human.
    if paths != sorted(paths) or _render_bundle(paths, digests) != text:
        raise ResolveError(f"{BUNDLE_MANIFEST}: {side} is not sorted, "
                           "canonically formatted JSON; resolve by hand")
    return set(paths)


def _bundle_base_paths(base):
    """Return the module paths named in a reconstructed base.

    A `zdiff3` base need not be valid JSON (see `split_conflict`), so read
    each `"path"` line rather than parsing the document. Every line must
    still have a canonical shape, so no base entry can be skipped.
    """
    members = []
    for line, in_section in base:
        match = BUNDLE_LINE_RE.fullmatch(line)
        if match is None:
            raise ResolveError(f"{BUNDLE_MANIFEST}: base is not canonically "
                               "formatted; resolve by hand")
        if match["path"] is not None:
            members.append((match["path"].decode("utf-8"), None, in_section))
    return {path for path, _ in _base_members(members, BUNDLE_MANIFEST)}


def _check_theory_path(path):
    """Mirror the bundle loader's module path policy."""
    parts = path.split("/")
    if (len(parts) < 3 or parts[0] != "theory" or parts[1] != "Anneal"
            or not path.endswith(".lean")
            or not all(LEAN_IDENT_RE.fullmatch(part)
                       for part in parts[1:-1] + [parts[-1][:-len(".lean")]])):
        raise ResolveError(f"{BUNDLE_MANIFEST}: {path} does not name a module "
                           "under theory/Anneal/")


def resolve_bundle_manifest(root, data):
    """Return the resolved bytes of a conflicted theory bundle manifest."""
    ours_bytes, base_bytes, theirs_bytes = split_conflict(data)
    ours = _bundle_paths(ours_bytes, "ours")
    theirs = _bundle_paths(theirs_bytes, "theirs")
    if ours == theirs:
        paths = ours
    elif base_bytes is None:
        raise ResolveError(f"{BUNDLE_MANIFEST}: sides bundle different modules "
                           "and there is no base section (use "
                           "merge.conflictStyle=diff3); resolve by hand")
    else:
        paths = _merge_sets(ours, _bundle_base_paths(base_bytes), theirs)
    paths = sorted(paths)
    if REQUIRED_THEORY_MODULE not in paths:
        raise ResolveError(f"{BUNDLE_MANIFEST}: merge drops {REQUIRED_THEORY_MODULE}")
    digests = {}
    for path in paths:
        _check_theory_path(path)
        content = _checked_input(root, path)
        try:
            content.decode("utf-8")
        except UnicodeError:
            raise ResolveError(f"{path}: expected UTF-8 Lean source") from None
        digests[path] = hashlib.sha256(content).hexdigest()
    _check_index(root, paths)
    return _render_bundle(paths, digests).encode("utf-8")


RESOLVERS = {ROOT_MANIFEST: resolve_root_manifest, BUNDLE_MANIFEST: resolve_bundle_manifest}


def _manifest_path(root, name):
    path = root / name
    current = root
    for part in PurePosixPath(name).parts:
        current = current / part
        if current.is_symlink():
            raise ResolveError(f"{name}: expected a regular file without symlinks")
    if not path.is_file():
        raise ResolveError(f"{name}: expected an existing regular file")
    return path


def resolve(root, names=None):
    """Resolve the named manifests, or every conflicted one, atomically.

    Return the list of rewritten manifest names. Compute every result before
    replacing any file so that a failure leaves all manifests untouched.
    """
    explicit = names is not None
    names = list(TARGETS.values()) if names is None else names
    unmerged = [] if explicit else unmerged_paths(root, names)
    planned = []
    for name in names:
        path = _manifest_path(root, name)
        original = path.read_bytes()
        if not explicit and not has_conflict_markers(original, "<|=>"):
            if name in unmerged:
                raise ResolveError(f"{name}: Git records a conflict but the file "
                                   "has no markers; resolve its membership by "
                                   "hand, then name it to refresh its digests")
            continue
        resolved = RESOLVERS[name](root, original)
        if resolved != original:
            planned.append((path, resolved))
    staged = []
    try:
        for path, resolved in planned:
            with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as file:
                staged.append((Path(file.name), path))
                file.write(resolved)
                os.fchmod(file.fileno(), stat.S_IMODE(path.stat().st_mode))
        for temporary, path in staged:
            os.replace(temporary, path)
    finally:
        for temporary, _ in staged:
            temporary.unlink(missing_ok=True)
    return [str(path.relative_to(root)) for path, _ in planned]


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=_CI_DIR.parent,
                        help="Anneal workspace root (default: %(default)s)")
    parser.add_argument("targets", nargs="*", choices=sorted(TARGETS),
                        help="manifests whose membership is already resolved by "
                             "hand, to refresh only their digests (default: "
                             "every manifest with conflict markers)")
    arguments = parser.parse_args()
    root = arguments.root.resolve()
    names = [TARGETS[target] for target in arguments.targets] or None
    try:
        changed = resolve(root, names)
    except (OSError, UnicodeError, ResolveError) as error:
        print(f"cannot resolve pin manifests: {error}", file=sys.stderr)
        return 1
    for name in changed:
        print(f"Resolved {name}; review and `git add` it.")
    if not changed:
        print("No pin manifest needed changes.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
