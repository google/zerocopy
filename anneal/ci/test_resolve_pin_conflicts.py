# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Exercise pin-manifest conflict resolution and its fail-closed boundaries."""

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

_CI_DIR = Path(__file__).resolve().parent
if str(_CI_DIR) not in sys.path:
    sys.path.insert(0, str(_CI_DIR))

import resolve_pin_conflicts as resolver  # noqa: E402


SCRIPT = Path(__file__).resolve().parent / "resolve_pin_conflicts.py"
ANNEAL_ROOT = Path(__file__).resolve().parent.parent
HEADER = b"# Pinned build inputs.\n\n"
ZERO = "0" * 64


def sha(data):
    return hashlib.sha256(data).hexdigest()


def conflict(ours, theirs, base=None, before=b"", after=b""):
    """Render one conflict hunk the way Git writes it."""
    hunk = b"<<<<<<< HEAD\n" + ours
    if base is not None:
        hunk += b"||||||| parent of 1234abc (change)\n" + base
    return before + hunk + b"=======\n" + theirs + b">>>>>>> 1234abc (change)\n" + after


def root_entry(name, digest=ZERO, mode=b"  "):
    return digest.encode() + mode + name.encode() + b"\n"


def bundle_text(paths, digest=lambda path: ZERO):
    return resolver._render_bundle(paths, {path: digest(path) for path in paths}).encode()


class Fixture(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="anneal-pin-resolve-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        (self.root / "trusted").mkdir()
        (self.root / "theory/Anneal").mkdir(parents=True)
        self.inputs = {}
        for name in ["Cargo.toml", "Cargo.lock", "flake.nix", "flake.lock",
                     "theory/Anneal/MirWp.lean", "theory/Anneal/A.lean",
                     "theory/Anneal/B.lean", "theory/Anneal/C.lean"]:
            self.write_input(name, f"contents of {name}\n".encode())
        self.root_manifest = self.root / resolver.ROOT_MANIFEST
        self.bundle_manifest = self.root / resolver.BUNDLE_MANIFEST
        # Default runs inspect both manifests; start each without conflicts.
        self.root_manifest.write_bytes(HEADER + root_entry("Cargo.toml"))
        self.bundle_manifest.write_bytes(bundle_text([resolver.REQUIRED_THEORY_MODULE]))

    def write_input(self, name, data):
        (self.root / name).write_bytes(data)
        self.inputs[name] = data

    def digest(self, name):
        return sha(self.inputs[name])

    def assert_rejected(self, path, data, message, names=None):
        path.write_bytes(data)
        with self.assertRaisesRegex(resolver.ResolveError, message):
            resolver.resolve(self.root, names)
        self.assertEqual(path.read_bytes(), data)


class SplitConflictTests(unittest.TestCase):
    def test_two_way_has_no_base(self):
        data = conflict(b"a\n", b"b\n", before=b"x\n", after=b"y\n")
        self.assertEqual(resolver.split_conflict(data), (b"x\na\ny\n", None, b"x\nb\ny\n"))

    def test_diff3_and_zdiff3_bases(self):
        data = conflict(b"a\n", b"b\n", b"c\n", after=b"y\n")
        self.assertEqual(resolver.split_conflict(data),
                         (b"a\ny\n", [(b"c\n", True), (b"y\n", False)], b"b\ny\n"))
        # A zdiff3 hunk can have an empty side and an empty base.
        data = conflict(b"a\n", b"", b"")
        self.assertEqual(resolver.split_conflict(data), (b"a\n", [], b""))

    def test_base_requires_every_hunk(self):
        data = conflict(b"a\n", b"b\n", b"c\n") + conflict(b"d\n", b"e\n")
        self.assertIsNone(resolver.split_conflict(data)[1])

    def test_malformed_markers_rejected(self):
        for data in [b"<<<<<<< HEAD\na\n=======\nb\n",
                     b"<<<<<<< HEAD\n<<<<<<< HEAD\n",
                     b"=======\n",
                     b"<<<<<<< HEAD\na\n>>>>>>> x\n",
                     b"<<<<<<< HEAD\n=======\n||||||| base\n>>>>>>> x\n"]:
            with self.subTest(data=data):
                with self.assertRaises(resolver.ResolveError):
                    resolver.split_conflict(data)

    def test_base_members_prefer_base_section_copies(self):
        members = [("a", 1, False), ("b", 2, True), ("a", 3, True), ("b", 4, False)]
        self.assertEqual(resolver._base_members(members, "m"), [("b", 2), ("a", 3)])
        for members in ([("a", 1, True), ("a", 2, True)], [("a", 1, False), ("a", 2, False)]):
            with self.assertRaisesRegex(resolver.ResolveError, "base lists a twice"):
                resolver._base_members(members, "m")

    def test_marker_detection_ignores_lookalikes(self):
        self.assertFalse(resolver.has_conflict_markers(b"-- <<<<<<< not a marker\n<<<<<<<<\n"))
        self.assertFalse(resolver.has_conflict_markers(b"=======\n"))
        self.assertTrue(resolver.has_conflict_markers(b"=======\n", "<|=>"))
        self.assertTrue(resolver.has_conflict_markers(b"a\n>>>>>>> theirs\n"))
        self.assertTrue(resolver.has_conflict_markers(b"<<<<<<<\r\n"))


class RootManifestTests(Fixture):
    def entries(self, *names):
        return b"".join(root_entry(name, ZERO) for name in names)

    def resolved_entries(self, *names):
        return b"".join(root_entry(name, self.digest(name)) for name in names)

    def test_identical_membership_recomputes_digests(self):
        data = HEADER + conflict(
            root_entry("Cargo.toml", "1" * 64), root_entry("Cargo.toml", "2" * 64),
            after=root_entry("Cargo.lock", "3" * 64, b" *"))
        self.root_manifest.write_bytes(data)
        self.assertEqual(resolver.resolve(self.root), [resolver.ROOT_MANIFEST])
        self.assertEqual(self.root_manifest.read_bytes(),
                         HEADER + root_entry("Cargo.toml", self.digest("Cargo.toml"))
                         + root_entry("Cargo.lock", self.digest("Cargo.lock"), b" *"))

    def test_three_way_add_add_keeps_ours_before_theirs(self):
        base = self.entries("Cargo.toml")
        data = HEADER + conflict(base + self.entries("flake.nix"),
                                 base + self.entries("flake.lock"), base)
        self.root_manifest.write_bytes(data)
        resolver.resolve(self.root)
        self.assertEqual(self.root_manifest.read_bytes(), HEADER + self.resolved_entries(
            "Cargo.toml", "flake.nix", "flake.lock"))

    def test_three_way_add_remove_and_shared_add(self):
        base = self.entries("Cargo.toml", "Cargo.lock")
        ours = self.entries("Cargo.toml", "flake.nix", "Cargo.lock")
        theirs = self.entries("Cargo.toml", "flake.nix")
        self.root_manifest.write_bytes(HEADER + conflict(ours, theirs, base))
        resolver.resolve(self.root)
        self.assertEqual(self.root_manifest.read_bytes(),
                         HEADER + self.resolved_entries("Cargo.toml", "flake.nix"))

    def test_zdiff3_lifted_common_entry(self):
        # `zdiff3` hoists the shared `Cargo.lock` addition out of the hunk, so
        # the reconstructed base wrongly contains it; both sides keep it anyway.
        data = HEADER + conflict(self.entries("flake.nix"), self.entries("flake.lock"), b"",
                                 before=self.entries("Cargo.toml", "Cargo.lock"))
        self.root_manifest.write_bytes(data)
        resolver.resolve(self.root)
        self.assertEqual(self.root_manifest.read_bytes(), HEADER + self.resolved_entries(
            "Cargo.toml", "Cargo.lock", "flake.nix", "flake.lock"))

    def test_zdiff3_hoisted_copy_of_base_entry(self):
        # True base: Cargo.lock, Cargo.toml. Both sides drop Cargo.lock and
        # append after Cargo.toml, so `zdiff3` hoists their shared leading
        # Cargo.toml out of the hunk while the base section still lists it.
        data = HEADER + conflict(self.entries("flake.nix"), self.entries("flake.lock"),
                                 self.entries("Cargo.lock", "Cargo.toml"),
                                 before=self.entries("Cargo.toml"))
        self.root_manifest.write_bytes(data)
        resolver.resolve(self.root)
        self.assertEqual(self.root_manifest.read_bytes(), HEADER + self.resolved_entries(
            "Cargo.toml", "flake.nix", "flake.lock"))

    def test_malformed_base_line_rejected(self):
        # Skipping the uppercase base entry would re-add the Cargo.lock pin
        # that ours removed.
        base = self.entries("Cargo.toml") + root_entry("Cargo.lock", "A" * 64)
        data = HEADER + conflict(self.entries("Cargo.toml"),
                                 self.entries("Cargo.toml", "Cargo.lock", "flake.nix"), base)
        self.assert_rejected(self.root_manifest, data, "malformed base line")
        base = self.entries("Cargo.toml", "Cargo.lock", "Cargo.lock")
        data = HEADER + conflict(self.entries("Cargo.toml"),
                                 self.entries("Cargo.toml", "Cargo.lock", "flake.nix"), base)
        self.assert_rejected(self.root_manifest, data, "base lists Cargo.lock twice")

    def test_unresolvable_membership_rejected(self):
        base = self.entries("Cargo.toml", "Cargo.lock")
        cases = {
            "no base section": conflict(self.entries("Cargo.toml"),
                                        self.entries("Cargo.lock")),
            "reorders": conflict(self.entries("Cargo.lock", "Cargo.toml"),
                                 self.entries("Cargo.toml"), base),
            "different positions": conflict(
                self.entries("flake.nix", "Cargo.toml", "Cargo.lock"),
                self.entries("Cargo.toml", "Cargo.lock", "flake.nix"), base),
            "checksum mode": conflict(
                root_entry("Cargo.toml", mode=b" *") + self.entries("Cargo.lock", "flake.nix"),
                self.entries("Cargo.toml", "Cargo.lock", "flake.lock"), base),
            "removes every entry": conflict(self.entries("Cargo.lock"),
                                            self.entries("Cargo.toml"), base),
        }
        for message, conflicted in cases.items():
            with self.subTest(message=message):
                self.assert_rejected(self.root_manifest, HEADER + conflicted, message)

    def test_comment_drift_rejected(self):
        for data in [
                conflict(b"# One.\n", b"# Two.\n", after=self.entries("Cargo.toml")),
                conflict(b"# One.\n" + self.entries("Cargo.toml"),
                         b"# Two.\n" + self.entries("Cargo.toml", "Cargo.lock"),
                         b"# One.\n" + self.entries("Cargo.toml")),
                conflict(self.entries("Cargo.toml") + b"# Interleaved.\n"
                         + self.entries("Cargo.lock"),
                         self.entries("Cargo.toml"), self.entries("Cargo.toml"))]:
            with self.subTest(data=data):
                self.assert_rejected(self.root_manifest, HEADER + data, "resolve by hand")

    def test_unready_inputs_rejected(self):
        data = HEADER + conflict(self.entries("Cargo.toml"),
                                 root_entry("Cargo.toml", "1" * 64))
        self.write_input("Cargo.toml", conflict(b"a\n", b"b\n"))
        self.assert_rejected(self.root_manifest, data, "resolve this input's conflict")
        (self.root / "Cargo.toml").unlink()
        self.assert_rejected(self.root_manifest, data, "missing pinned input")
        (self.root / "Cargo.toml").symlink_to("Cargo.lock")
        self.assert_rejected(self.root_manifest, data, "without symlinks")

    def test_symlinked_directory_and_escaping_paths_rejected(self):
        (self.root / "real").mkdir()
        (self.root / "real/Cargo.toml").write_bytes(b"x\n")
        (self.root / "alias").symlink_to("real")
        for name, message in [("alias/Cargo.toml", "without symlinks"),
                              ("../Cargo.toml", "canonical relative path"),
                              ("trusted/root-manifest.sha256", "cannot pin itself")]:
            with self.subTest(name=name):
                data = HEADER + conflict(self.entries(name), root_entry(name, "1" * 64))
                self.assert_rejected(self.root_manifest, data, message)

    def test_updater_grammar_applies(self):
        data = HEADER + conflict(b"not an entry\n", b"not an entry\n",
                                 after=self.entries("Cargo.toml"))
        self.assert_rejected(self.root_manifest, data, "malformed checksum entry")


class BundleManifestTests(Fixture):
    def paths(self, *stems):
        return sorted(f"theory/Anneal/{stem}.lean" for stem in stems)

    def resolved(self, *stems):
        return bundle_text(self.paths(*stems), self.digest)

    def lines(self, *stems):
        return bundle_text(self.paths(*stems)).splitlines(keepends=True)

    def test_identical_membership_recomputes_digests(self):
        ours = bundle_text(self.paths("A", "MirWp"), lambda path: "1" * 64)
        theirs = bundle_text(self.paths("A", "MirWp"), lambda path: "2" * 64)
        # Conflict only the digest lines, as Git would.
        data = b"".join(o if o == t else conflict(o, t)
                        for o, t in zip(ours.splitlines(True), theirs.splitlines(True)))
        self.bundle_manifest.write_bytes(data)
        self.assertEqual(resolver.resolve(self.root), [resolver.BUNDLE_MANIFEST])
        self.assertEqual(self.bundle_manifest.read_bytes(), self.resolved("A", "MirWp"))

    def test_three_way_add_add_and_add_remove(self):
        cases = [(("MirWp",), ("A", "MirWp"), ("B", "MirWp"), ("A", "B", "MirWp")),
                 (("A", "MirWp"), ("A", "B", "MirWp"), ("MirWp",), ("B", "MirWp")),
                 (("A", "MirWp"), ("A", "C", "MirWp"), ("A", "C", "MirWp"),
                  ("A", "C", "MirWp"))]
        for base, ours, theirs, expected in cases:
            with self.subTest(base=base, ours=ours, theirs=theirs):
                data = conflict(bundle_text(self.paths(*ours)), bundle_text(self.paths(*theirs)),
                                bundle_text(self.paths(*base)))
                self.bundle_manifest.write_bytes(data)
                resolver.resolve(self.root)
                self.assertEqual(self.bundle_manifest.read_bytes(), self.resolved(*expected))

    def test_unresolvable_membership_and_drift_rejected(self):
        base = bundle_text(self.paths("MirWp"))
        ours = bundle_text(self.paths("A", "MirWp"))
        theirs = bundle_text(self.paths("B", "MirWp"))
        reordered = json.loads(ours)
        reordered["modules"].reverse()
        extra = json.loads(ours)
        extra["generator"] = "x"
        cases = {
            "no base section": conflict(ours, theirs),
            "schema version": conflict(ours, ours.replace(b'"schema_version": 1',
                                                          b'"schema_version": 2'), base),
            "not sorted": conflict((json.dumps(reordered, indent=2) + "\n").encode(),
                                   theirs, base),
            "canonically formatted": conflict(ours, ours.replace(b"\n  ", b"\n    "), base),
            "schema version 1": conflict(ours, (json.dumps(extra, indent=2) + "\n").encode(),
                                         base),
            "drops theory/Anneal/MirWp.lean": conflict(
                bundle_text(self.paths("A")), bundle_text(self.paths("A", "MirWp")), base),
            "duplicate JSON key": conflict(ours, b'{"schema_version": 1, '
                                           b'"schema_version": 1, "modules": []}\n', base),
        }
        for message, data in cases.items():
            with self.subTest(message=message):
                self.assert_rejected(self.bundle_manifest, data, message)

    def test_zdiff3_base_and_invalid_base_lines(self):
        # Real `zdiff3` output hoists the shared `    {` line of two additions
        # before the first base entry, leaving a base that is not JSON.
        ours, theirs, base = (bundle_text(self.paths(*stems)).splitlines(True)
                              for stems in (("A", "MirWp"), ("B", "MirWp"), ("MirWp",)))
        data = b"".join(ours[:4]) + conflict(b"".join(ours[4:7]), b"".join(theirs[4:7]),
                                             b"", after=b"".join(ours[7:]))
        self.bundle_manifest.write_bytes(data)
        resolver.resolve(self.root)
        self.assertEqual(self.bundle_manifest.read_bytes(), self.resolved("A", "B", "MirWp"))
        # A compact base could hide an entry from line-based reading.
        compact = (json.dumps(json.loads(b"".join(base)), separators=(",", ":"))
                   + "\n").encode()
        self.assert_rejected(self.bundle_manifest, conflict(
            b"".join(ours), b"".join(theirs), compact), "base is not canonically formatted")

    def test_unready_or_invalid_modules_rejected(self):
        data = conflict(bundle_text(self.paths("A", "MirWp")),
                        bundle_text(self.paths("B", "MirWp")), bundle_text(self.paths("MirWp")))
        self.write_input("theory/Anneal/A.lean", conflict(b"a\n", b"b\n", b"c\n"))
        self.assert_rejected(self.bundle_manifest, data, "resolve this input's conflict")
        (self.root / "theory/Anneal/A.lean").unlink()
        (self.root / "theory/Anneal/A.lean").symlink_to("B.lean")
        self.assert_rejected(self.bundle_manifest, data, "without symlinks")
        (self.root / "theory/Anneal/A.lean").unlink()
        self.assert_rejected(self.bundle_manifest, data, "missing pinned input")
        self.write_input("theory/Anneal/A.lean", b"\xff\n")
        self.assert_rejected(self.bundle_manifest, data, "UTF-8")
        for path in ["theory/Anneal/a-b.lean", "theory/Other/A.lean", "theory/Anneal/A.olean"]:
            with self.subTest(path=path):
                paths = sorted([path, resolver.REQUIRED_THEORY_MODULE])
                self.assert_rejected(self.bundle_manifest, conflict(
                    bundle_text(paths), bundle_text(paths, lambda path: "1" * 64)),
                    "does not name a module")


class EndToEndTests(Fixture):
    def test_failure_in_one_manifest_leaves_both_untouched(self):
        root_data = HEADER + conflict(root_entry("Cargo.toml"), root_entry("Cargo.toml", "1" * 64))
        bundle_data = conflict(bundle_text(["theory/Anneal/MirWp.lean"]),
                               bundle_text(["theory/Anneal/A.lean", "theory/Anneal/MirWp.lean"]))
        self.root_manifest.write_bytes(root_data)
        self.bundle_manifest.write_bytes(bundle_data)
        result = subprocess.run([sys.executable, "-I", "-B", str(SCRIPT), "--root",
                                 str(self.root)], capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, 1, result)
        self.assertIn("no base section", result.stderr)
        self.assertEqual(self.root_manifest.read_bytes(), root_data)
        self.assertEqual(self.bundle_manifest.read_bytes(), bundle_data)
        self.assertEqual(sorted(p.name for p in (self.root / "trusted").iterdir()),
                         ["root-manifest.sha256"])

    def test_default_touches_only_conflicted_manifests(self):
        stale_root = HEADER + root_entry("Cargo.toml")
        self.root_manifest.write_bytes(stale_root)
        self.bundle_manifest.write_bytes(conflict(
            bundle_text(["theory/Anneal/MirWp.lean"]),
            bundle_text(["theory/Anneal/MirWp.lean"], lambda path: "1" * 64)))
        self.root_manifest.chmod(0o640)
        self.bundle_manifest.chmod(0o640)
        result = subprocess.run([sys.executable, "-I", "-B", str(SCRIPT), "--root",
                                 str(self.root)], capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, 0, result)
        self.assertEqual(self.root_manifest.read_bytes(), stale_root)
        self.assertEqual(self.bundle_manifest.read_bytes(), bundle_text(
            ["theory/Anneal/MirWp.lean"], self.digest))
        self.assertEqual(self.bundle_manifest.stat().st_mode & 0o777, 0o640)
        # Naming a manifest refreshes it even without markers.
        self.assertEqual(resolver.resolve(self.root, [resolver.ROOT_MANIFEST]),
                         [resolver.ROOT_MANIFEST])
        self.assertEqual(self.root_manifest.read_bytes(),
                         HEADER + root_entry("Cargo.toml", self.digest("Cargo.toml")))
        self.assertEqual(resolver.resolve(self.root), [])

    def test_stray_marker_in_manifest_rejected(self):
        data = HEADER + root_entry("Cargo.toml") + b"=======\n"
        self.assert_rejected(self.root_manifest, data, "unexpected conflict marker")

    def test_symlinked_manifest_rejected(self):
        (self.root / "elsewhere.sha256").write_bytes(HEADER + root_entry("Cargo.toml"))
        self.root_manifest.unlink()
        self.root_manifest.symlink_to("../elsewhere.sha256")
        with self.assertRaisesRegex(resolver.ResolveError, "without symlinks"):
            resolver.resolve(self.root, [resolver.ROOT_MANIFEST])

    @unittest.skipIf(shutil.which("git") is None, "git is unavailable")
    def test_unmerged_index_entry_rejected(self):
        def git(*arguments, data=None):
            return subprocess.run(["git", "-C", str(self.root), *arguments], input=data,
                                  capture_output=True, check=True).stdout
        git("init", "-q")
        blob = git("hash-object", "-w", "Cargo.toml").strip()
        # A modify/delete conflict leaves base and ours stages and no markers.
        git("update-index", "--index-info",
            data=b"100644 %s 1\tCargo.toml\n100644 %s 2\tCargo.toml\n" % (blob, blob))
        data = HEADER + conflict(root_entry("Cargo.toml"), root_entry("Cargo.toml", "1" * 64))
        self.assert_rejected(self.root_manifest, data, "unmerged pinned inputs: Cargo.toml")
        # An inherited `GIT_DIR` must not redirect the index lookup.
        with patch.dict(os.environ, {"GIT_DIR": str(self.root / "missing")}):
            self.assert_rejected(self.root_manifest, data, "unmerged pinned inputs")
        # A pinned name is a literal path, not a glob over unmerged files.
        self.write_input("Cargo*", b"glob\n")
        self.root_manifest.write_bytes(HEADER + conflict(
            root_entry("Cargo*"), root_entry("Cargo*", "1" * 64)))
        resolver.resolve(self.root)
        self.assertEqual(self.root_manifest.read_bytes(),
                         HEADER + root_entry("Cargo*", self.digest("Cargo*")))
        # An unmerged manifest without markers needs a human; once its
        # membership is settled, naming it refreshes the digests.
        manifest_blob = git("hash-object", "-w", resolver.ROOT_MANIFEST).strip()
        git("update-index", "--index-info", data=b"".join(
            b"100644 %s %d\t%s\n" % (manifest_blob, stage, resolver.ROOT_MANIFEST.encode())
            for stage in (1, 2, 3)))
        stale = HEADER + root_entry("flake.nix")
        self.assert_rejected(self.root_manifest, stale, "has no markers")
        resolver.resolve(self.root, [resolver.ROOT_MANIFEST])
        self.assertEqual(self.root_manifest.read_bytes(),
                         HEADER + root_entry("flake.nix", self.digest("flake.nix")))


@unittest.skipIf(shutil.which("git") is None, "git is unavailable")
class GitMergeTests(Fixture):
    """Resolve the markers that Git itself writes for concurrent pin edits."""

    def git(self, *arguments, check=True):
        environment = {"GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1",
                       "HOME": str(self.root), "PATH": os.environ.get("PATH", "")}
        return subprocess.run(["git", "-C", str(self.root), "-c", "user.name=Test",
                               "-c", "user.email=test@example.com", *arguments],
                              env=environment, capture_output=True, check=check)

    def commit_bundle(self, stems):
        paths = sorted(f"theory/Anneal/{stem}.lean" for stem in stems)
        self.bundle_manifest.write_bytes(bundle_text(paths, self.digest))
        self.root_manifest.write_bytes(HEADER + b"".join(
            root_entry(name, self.digest(name)) for name in ["Cargo.toml", *paths]))
        self.git("add", "-A")
        self.git("commit", "-q", "-m", " ".join(stems))

    def test_concurrent_module_additions(self):
        for style, resolvable in [("merge", False), ("diff3", True), ("zdiff3", True)]:
            with self.subTest(style=style):
                shutil.rmtree(self.root / ".git", ignore_errors=True)
                self.git("init", "-q", "-b", "main")
                self.commit_bundle(["MirWp"])
                self.git("checkout", "-q", "-b", "other")
                self.commit_bundle(["B", "MirWp"])
                self.git("checkout", "-q", "main")
                self.commit_bundle(["A", "MirWp"])
                merge = self.git("-c", f"merge.conflictStyle={style}", "merge", "-q",
                                 "other", check=False)
                self.assertNotEqual(merge.returncode, 0, merge)
                conflicted = (self.root_manifest.read_bytes(),
                              self.bundle_manifest.read_bytes())
                self.assertTrue(all(map(resolver.has_conflict_markers, conflicted)))
                if not resolvable:
                    with self.assertRaisesRegex(resolver.ResolveError, "no base section"):
                        resolver.resolve(self.root)
                    self.assertEqual((self.root_manifest.read_bytes(),
                                      self.bundle_manifest.read_bytes()), conflicted)
                    self.git("merge", "--abort")
                    continue
                self.assertEqual(sorted(resolver.resolve(self.root)),
                                 [resolver.BUNDLE_MANIFEST, resolver.ROOT_MANIFEST])
                paths = [f"theory/Anneal/{stem}.lean" for stem in ["A", "B", "MirWp"]]
                self.assertEqual(self.bundle_manifest.read_bytes(),
                                 bundle_text(paths, self.digest))
                self.assertEqual(self.root_manifest.read_bytes(), HEADER + b"".join(
                    root_entry(name, self.digest(name))
                    for name in ["Cargo.toml", *paths]))
                self.git("merge", "--abort")


class RepositoryTests(unittest.TestCase):
    def test_checked_in_manifests_are_fixed_points(self):
        # Resolution without markers must reproduce the reviewed bytes exactly,
        # which pins this tool to the repository's formatting conventions.
        for name, resolve in resolver.RESOLVERS.items():
            with self.subTest(name=name):
                original = (ANNEAL_ROOT / name).read_bytes()
                self.assertEqual(resolve(ANNEAL_ROOT, original), original)


if __name__ == "__main__":
    unittest.main()
