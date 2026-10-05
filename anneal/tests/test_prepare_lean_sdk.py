#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.

"""Tiny publisher fixtures: no Lean/Lake subprocesses or real payloads."""

import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import stat
import struct
import tempfile
import unittest
from unittest.mock import patch


SCRIPT = Path(__file__).resolve().parents[1] / "prepare-lean-sdk.py"
SPEC = importlib.util.spec_from_file_location("prepare_lean_sdk", SCRIPT)
publisher = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(publisher)


def write(path, contents):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(contents.encode() if isinstance(contents, str) else contents)


def native(platform="aarch64-darwin", payload=b"native producer bytes"):
    if platform.endswith("-linux"):
        header = bytearray(32)
        header[:6] = b"\x7fELF\x02\x01"
        struct.pack_into("<H", header, 18, 183 if platform.startswith("aarch64-") else 62)
    else:
        header = bytearray(b"\xcf\xfa\xed\xfe" + b"\0" * 28)
        struct.pack_into("<I", header, 4, 0x0100000C if platform.startswith("aarch64-") else 0x01000007)
    return bytes(header) + payload


def olean(payload=b"compiled producer bytes"):
    return b"olean\x02\x01" + publisher.VERSION.encode().ljust(33, b"\0") + publisher.COMPILER_HASH.encode() + payload


def module(owner, name, split=False, runtime=False, lake=False):
    path = Path(*name.split("."))
    source_root = owner / ("src/lean/lake" if lake else "src/lean") if runtime else owner
    lib = owner / ("lib/lean" if runtime else ".lake/build/lib/lean")
    write(source_root / path.with_suffix(".lean"), ("/- outer /- nested -/ comment -/\nmodule\n" if split else "") + "-- fixture\n")
    for family in publisher.SPLIT if split else publisher.LEGACY:
        write(lib / (str(path) + "." + family), "{}\n" if family == "ilean" else olean(name.encode()))


class PrepareLeanSdkTests(unittest.TestCase):
    def setUp(self):
        # Parent selects the assigned Data scratch root for local runs; CI may
        # use ordinary temporary scratch. Never use a source tree/global cache.
        # Retain cases as evidence, rather than deleting publisher output trees.
        scratch = os.environ.get("ANNEAL_SDK_TEST_ROOT")
        if scratch is not None:
            scratch = Path(scratch)
            scratch.mkdir(parents=True, exist_ok=True)
        self.case = Path(tempfile.mkdtemp(prefix=self._testMethodName + "-", dir=scratch))
        self.root = self.case / "archive"
        self.runtime = self.root / "lean"
        self.project = self.root / "aeneas/backends/lean"
        self.packages = self.root / "aeneas/packages"
        self.packages.mkdir(parents=True)
        self.platform = "aarch64-darwin"
        self.dependencies = {}
        inspection = patch.object(publisher, "native_dependencies", side_effect=lambda path, platform:
            self.dependencies.get(path.name, {"needed": [], "rpaths": [], "identity": None, "interpreter": None}))
        inspection.start()
        self.addCleanup(inspection.stop)
        for name in ("lean", "lake"):
            write(self.runtime / "bin" / name, native())
            (self.runtime / "bin" / name).chmod(0o755)
        write(self.runtime / "include/lean/lean.h", "/* runtime header */")
        write(self.runtime / "lib/libleanshared.dylib", native())
        write(self.project / "lean-toolchain", publisher.TOOLCHAIN + "\n")
        write(self.project / ".lake/build/lib/libaeneas_AeneasMeta.dylib", native())
        module(self.runtime, "Init", split=True, runtime=True)
        module(self.runtime, "Lake.Util", split=True, runtime=True, lake=True)
        module(self.project, "Aeneas")
        module(self.project, "Shared.A")
        module(self.packages / "batteries", "Shared.B")
        # Source-only packages do not become compiled exports.
        write(self.packages / "Cli/Cli.lean", "module\n")

    def catalog(self, exports=None):
        return publisher.make_catalog(self.runtime, self.project, self.packages, self.platform, exports)

    def reject_assembly(self, catalog):
        with self.assertRaises((ValueError, FileNotFoundError)):
            publisher.assemble(self.root, catalog)
        self.assertFalse((self.root / "lean-sdk").exists(), "rejection must precede output creation")

    def test_merges_exact_modules_and_preserves_real_launchers(self):
        catalog = self.catalog()
        original_inputs = {str(p.relative_to(self.root)): publisher.digest(p)
                           for p in self.root.rglob("*") if p.is_file()}
        with patch("subprocess.Popen", side_effect=AssertionError("subject spawn forbidden")):
            result = publisher.assemble(self.root, catalog)
        sdk = self.root / "lean-sdk"
        modules = json.loads((sdk / "modules.json").read_text())
        self.assertEqual(modules, {"schema": 1, "modules": ["Aeneas", "Init", "Lake.Util", "Shared.A", "Shared.B"]})
        self.assertEqual(result["modules_sha256"], publisher.digest(sdk / "modules.json"))
        self.assertEqual(result["runtime"], "../lean")
        self.assertEqual(result["source_roots"], ["src/lean"])
        self.assertEqual(result["plugins"][0]["name"], "aeneas_AeneasMeta")
        self.assertEqual((sdk / "src/lean/Lake/Util.lean").resolve(), self.runtime / "src/lean/lake/Lake/Util.lean")
        for name in ("lean", "lake"):
            self.assertFalse((sdk / "bin" / name).is_symlink())
            self.assertEqual((sdk / "bin" / name).read_bytes(), (self.runtime / "bin" / name).read_bytes())
        self.assertTrue((sdk / "lib/lean/Shared").is_dir())
        for name in ("A", "B"):
            self.assertTrue((sdk / "lib/lean/Shared" / (name + ".olean")).is_symlink())
        self.assertEqual({str(p.relative_to(sdk)) for p in sdk.rglob("*") if p.is_file() and not p.is_symlink()},
                         {"bin/lean", "bin/lake", "sdk.json", "modules.json", "publisher-catalog.json"})
        for path in sdk.rglob("*"):
            if not path.is_symlink():
                self.assertFalse(stat.S_IMODE(path.stat().st_mode) & 0o222)
            else:
                self.assertFalse(Path(os.readlink(path)).is_absolute())
        for relative, expected in original_inputs.items():
            self.assertEqual(publisher.digest(self.root / relative), expected)

    def test_rejects_duplicate_exact_module(self):
        module(self.packages / "other", "Shared.A")
        with self.assertRaisesRegex(ValueError, "duplicate exact module"):
            self.catalog()

    def test_expected_split_families_precede_candidate_inventory(self):
        catalog = self.catalog()
        for suffix in ("ilean", "olean.private", "olean.server", "ir"):
            path = self.runtime / "lib/lean" / ("Init." + suffix)
            old = path.read_bytes()
            path.unlink()
            self.reject_assembly(catalog)
            path.write_bytes(old)

    def test_missing_family_cannot_be_blessed_at_producer_capture(self):
        (self.runtime / "lib/lean/Init.olean.private").unlink()
        with self.assertRaises(FileNotFoundError):
            self.catalog()

    def test_missing_module_cannot_shrink_known_catalog(self):
        catalog = self.catalog()
        (self.project / ".lake/build/lib/lean/Aeneas.olean").unlink()
        self.reject_assembly(catalog)

    def test_orphan_module_family_rejected(self):
        (self.project / ".lake/build/lib/lean/Aeneas.olean").unlink()
        with self.assertRaisesRegex(ValueError, "orphan"):
            self.catalog()

    def test_source_content_change_rejected(self):
        catalog = self.catalog()
        write(self.project / "Aeneas.lean", "-- changed same provider source\n")
        self.reject_assembly(catalog)

    def test_module_content_change_rejected(self):
        catalog = self.catalog()
        write(self.project / ".lake/build/lib/lean/Aeneas.olean", olean(b"different"))
        self.reject_assembly(catalog)

    def test_missing_or_ambiguous_source_rejected(self):
        path = self.project / "Aeneas.lean"
        path.rename(self.project / "Aeneas.saved")
        with self.assertRaisesRegex(ValueError, "exactly one"):
            self.catalog()
        path.write_text("-- fixture\n")
        write(self.runtime / "src/lean/Lake/Util.lean", "module\n")
        with self.assertRaisesRegex(ValueError, "exactly one"):
            self.catalog()

    def test_wrong_compiler_header_rejected(self):
        write(self.project / ".lake/build/lib/lean/Aeneas.olean", olean().replace(publisher.COMPILER_HASH.encode(), b"0" * 40))
        with self.assertRaisesRegex(ValueError, "incompatible RC2"):
            self.catalog()

    def test_wrong_companion_compiler_rejected(self):
        write(self.runtime / "lib/lean/Init.ir", b"final compiler artifact")
        with self.assertRaisesRegex(ValueError, "incompatible RC2"):
            self.catalog()

    def test_wrong_native_architecture_rejected(self):
        write(self.project / ".lake/build/lib/libaeneas_AeneasMeta.dylib", native("x86_64-darwin"))
        with self.assertRaisesRegex(ValueError, "incompatible native"):
            self.catalog()

    def test_irrelevant_source_administrative_link_is_not_exported(self):
        (self.project / ".lake/packages").symlink_to(self.case / "historical-missing-link")
        catalog = self.catalog()
        publisher.assemble(self.root, catalog)
        self.assertFalse((self.root / "lean-sdk/.lake/packages").exists())

    def test_poisoned_native_candidate_rejected(self):
        catalog = self.catalog()
        write(self.project / ".lake/build/lib/libaeneas_AeneasMeta.dylib", native(payload=b"swapped plugin"))
        self.reject_assembly(catalog)

    def test_runtime_support_loss_or_corruption_rejected(self):
        catalog = self.catalog()
        path = self.runtime / "include/lean/lean.h"
        path.rename(self.runtime / "include/lean/old.h")
        self.reject_assembly(catalog)
        path.write_text("/* wrong runtime */")
        (self.runtime / "include/lean/old.h").rename(self.case / "saved-runtime.h")
        self.reject_assembly(catalog)

    def test_runtime_support_merges_beside_module_namespace(self):
        write(self.runtime / "lib/lean/Lake/support.h", "/* native support */")
        write(self.runtime / "lib/lean/Lake/support.json", '{"runtime":"data"}')
        write(self.runtime / "lib/lean/Lake/data", "extensionless runtime data")
        write(self.runtime / "lib/lean/Support/runtime.h", "/* native support directory */")
        publisher.assemble(self.root, self.catalog())
        for name in ("Lake/support.h", "Lake/support.json", "Lake/data", "Support/runtime.h"):
            sdk_path = self.root / "lean-sdk/lib/lean" / name
            self.assertEqual(sdk_path.read_bytes(), (self.runtime / "lib/lean" / name).read_bytes())
            self.assertTrue(sdk_path.resolve().is_relative_to(self.runtime))

    def test_dangling_and_escaping_module_links_rejected(self):
        catalog = self.catalog()
        artifact = self.project / ".lake/build/lib/lean/Aeneas.olean"
        artifact.unlink()
        artifact.symlink_to(self.case / "absent")
        self.reject_assembly(catalog)
        artifact.unlink()
        outside = self.case / "foreign.olean"
        outside.write_bytes(olean(b"Aeneas"))
        artifact.symlink_to(outside)
        self.reject_assembly(catalog)

    def test_cross_provider_family_mixing_rejected(self):
        catalog = self.catalog()
        catalog["modules"]["Shared.A"]["artifacts"]["ilean"] = copy.deepcopy(catalog["modules"]["Shared.B"]["artifacts"]["ilean"])
        self.reject_assembly(catalog)

    def test_tampered_source_format_family_manifest_rejected(self):
        catalog = self.catalog()
        del catalog["modules"]["Init"]["artifacts"]["ir"]
        self.reject_assembly(catalog)

    def test_source_profile_ignores_nested_comments_and_lookalikes(self):
        source = self.case / "Profile.lean"
        write(source, "-- module\n/- module /- nesting -/ -/\nmodule -- comment\n")
        self.assertTrue(publisher.is_split(source))
        write(source, "-- module\nimport Aeneas\n")
        self.assertFalse(publisher.is_split(source))
        write(source, "moduleName\n")
        self.assertFalse(publisher.is_split(source))
        write(source, "/- incomplete")
        with self.assertRaises(ValueError):
            publisher.is_split(source)

    def test_intended_mathlib_exports_require_compiled_inputs(self):
        module(self.packages / "mathlib", "Mathlib.Keep", split=True)
        module(self.packages / "mathlib", "Mathlib.Drop", split=True)
        catalog = self.catalog({"Mathlib.Keep"})
        self.assertIn("Mathlib.Keep", catalog["modules"])
        self.assertNotIn("Mathlib.Drop", catalog["modules"])
        with self.assertRaisesRegex(ValueError, "intended Mathlib export"):
            self.catalog({"Mathlib.Missing"})

    def test_create_only_assembly(self):
        catalog = self.catalog()
        publisher.assemble(self.root, catalog)
        with self.assertRaises(FileExistsError):
            publisher.assemble(self.root, catalog)

    def test_id_excludes_rust_and_envelope_and_survives_relocation(self):
        catalog = self.catalog()
        other = self.case / "other-archive"
        shutil.copytree(self.root, other, symlinks=True)
        write(other / "rust/bin/rustc", "unrelated Rust update")
        write(other / "metadata.json", "different archive envelope metadata")
        first = publisher.assemble(self.root, catalog)
        second = publisher.assemble(other, catalog)
        self.assertEqual(first["id"], second["id"])
        renamed = self.case / "relocated"
        other.rename(renamed)
        sdk = renamed / "lean-sdk"
        for path in sdk.rglob("*"):
            if path.is_symlink():
                self.assertTrue(path.exists())
        self.assertEqual((sdk / "src/lean/Aeneas.lean").resolve(), renamed / "aeneas/backends/lean/Aeneas.lean")
        publication = json.loads((sdk / "publisher-catalog.json").read_text())["published"]
        self.assertEqual(first["id"], hashlib.sha256(publisher.encoded(publication)).hexdigest())

    def test_changed_consumed_source_changes_identity_after_new_catalog(self):
        original = self.catalog()
        other = self.case / "updated"
        shutil.copytree(self.root, other)
        write(other / "aeneas/backends/lean/Aeneas.lean", "-- changed producer source\n")
        fresh = publisher.make_catalog(other / "lean", other / "aeneas/backends/lean", other / "aeneas/packages", self.platform)
        self.assertNotEqual(publisher.assemble(self.root, original)["id"], publisher.assemble(other, fresh)["id"])

    def test_native_relocation_is_explicit_and_final_bytes_are_pinned(self):
        # Convert this tiny tuple to Linux headers before trusted capture.
        self.platform = "aarch64-linux"
        for name in ("lean", "lake"):
            write(self.runtime / "bin" / name, native(self.platform))
        old_plugin = self.project / ".lake/build/lib/libaeneas_AeneasMeta.dylib"
        old_plugin.rename(self.case / "saved-mac-plugin")
        plugin = self.project / ".lake/build/lib/libaeneas_AeneasMeta.so"
        write(plugin, native(self.platform))
        # RC2's unconsumed leantar helper has a different architecture. Its
        # transformed bytes are pinned, without claiming it supports this facet.
        helper = self.runtime / "bin/leantar"
        write(helper, native("x86_64-linux"))
        helper.chmod(0o755)
        catalog = self.catalog()
        write(plugin, native(self.platform, b"trusted post-relocation bytes"))
        write(helper, native("x86_64-linux", b"trusted helper relocation"))
        self.reject_assembly(catalog)
        result = publisher.assemble(self.root, catalog, allow_native_relocation=True)
        published = json.loads((self.root / "lean-sdk/publisher-catalog.json").read_text())
        self.assertEqual(published["published"]["plugin"]["sha256"], publisher.digest(plugin))
        self.assertNotEqual(published["published"]["plugin"]["sha256"], catalog["plugin"]["producer_sha256"])
        self.assertEqual(result["platform"], self.platform)

    def test_native_inspection_parsers(self):
        macho = """cmd LC_ID_DYLIB
name @rpath/libSelf.dylib (offset 24)
cmd LC_RPATH
path @loader_path (offset 12)
cmd LC_LOAD_DYLIB
name @rpath/libDependency.dylib (offset 24)
cmd LC_LOAD_WEAK_DYLIB
name /usr/lib/libSystem.B.dylib (offset 24)
"""
        result = publisher.parse_native(macho, self.platform)
        self.assertEqual(result["identity"], "@rpath/libSelf.dylib")
        self.assertEqual(result["rpaths"], ["@loader_path"])
        self.assertEqual(result["needed"], ["@rpath/libDependency.dylib", "/usr/lib/libSystem.B.dylib"])
        elf = """0x (NEEDED) Shared library: [libc.so.6]
0x (RUNPATH) Library runpath: [$ORIGIN/../lib:$ORIGIN]
0x (SONAME) Library soname: [libSelf.so]
[Requesting program interpreter: /lib64/ld-linux-x86-64.so.2]
"""
        result = publisher.parse_native(elf, "x86_64-linux")
        self.assertEqual(result["needed"], ["libc.so.6"])
        self.assertEqual(result["rpaths"], ["$ORIGIN/../lib", "$ORIGIN"])
        self.assertEqual(result["interpreter"], "/lib64/ld-linux-x86-64.so.2")
        with self.assertRaises(ValueError):
            publisher.parse_native("0x (NEEDED) malformed", "x86_64-linux")

    def test_empty_elf_search_path_is_rejected_instead_of_using_current_directory(self):
        # patchelf --set-rpath "" retains an empty RUNPATH tag. The producer
        # must remove the tag; accepting it would admit a cwd search provider.
        parsed = publisher.parse_native("0x (RUNPATH) Library runpath: []", "x86_64-linux")
        self.assertEqual(parsed["rpaths"], [""])
        self.dependencies["lean"] = parsed
        self.reject_assembly(self.catalog())

    def test_recursive_native_provider_closure_and_system_policy(self):
        self.dependencies["lean"] = {"needed": ["@rpath/libleanshared.dylib"], "rpaths": ["@executable_path/../lib"], "identity": None, "interpreter": "/usr/lib/dyld"}
        self.dependencies["libleanshared.dylib"] = {"needed": ["/usr/lib/libSystem.B.dylib"], "rpaths": [], "identity": "@rpath/libleanshared.dylib", "interpreter": None}
        result = publisher.assemble(self.root, self.catalog())
        published = json.loads((self.root / "lean-sdk/publisher-catalog.json").read_text())["published"]
        self.assertIn("lean/lib/libleanshared.dylib", published["native_closure"]["images"])
        self.assertEqual(published["native_closure"]["system"], ["/usr/lib/libSystem.B.dylib"])
        self.assertIn("../aeneas/backends/lean/.lake/build/lib", result["loader_roots"])

    def test_missing_unaccounted_or_escaping_native_dependency_rejected(self):
        catalog = self.catalog()
        for reference in ("@rpath/libMissing.dylib", "/nix/store/package/libDependency.dylib", "../foreign.dylib"):
            self.dependencies["lean"] = {"needed": [reference], "rpaths": [], "identity": None, "interpreter": None}
            self.reject_assembly(catalog)
        self.dependencies["lean"] = {"needed": ["@rpath/libOther.dylib"], "rpaths": [], "identity": None, "interpreter": None}
        write(self.project / ".lake/build/lib/libOther.dylib", native())
        self.reject_assembly(catalog)  # Not recorded by trusted producer.

    def test_residual_native_rpath_identity_and_interpreter_rejected(self):
        catalog = self.catalog()
        for key, value in (("rpaths", ["/nix/store/lib"]), ("identity", "/private/tmp/producer/libSelf.dylib"),
                           ("interpreter", "/nix/store/glibc/ld.so")):
            information = {"needed": [], "rpaths": [], "identity": None, "interpreter": None}
            information[key] = value
            self.dependencies["lean"] = information
            self.reject_assembly(catalog)

    def test_ambiguous_native_provider_rejected(self):
        write(self.project / ".lake/build/lib/libleanshared.dylib", native())
        self.dependencies["lean"] = {"needed": ["@rpath/libleanshared.dylib"], "rpaths": [], "identity": None, "interpreter": None}
        self.reject_assembly(self.catalog())

    def test_darwin_relocation_requires_success_and_fresh_reinspection(self):
        plugin = self.project / ".lake/build/lib/libaeneas_AeneasMeta.dylib"
        information = {"needed": [], "rpaths": [], "identity": "/private/tmp/producer/libaeneas_AeneasMeta.dylib", "interpreter": None}
        self.dependencies[plugin.name] = information
        def relocate(arguments):
            if arguments[0] == "codesign":
                self.assertIn("--timestamp=none", arguments)
                return ""
            self.assertEqual(arguments[:2], ["install_name_tool", "-id"])
            information["identity"] = arguments[2]
            return ""
        with patch.object(publisher, "_tool", side_effect=relocate) as commands:
            publisher.loader_closure(self.root, plugin, self.platform, relocate=True)
            self.assertEqual(commands.call_count, 2)
        information["identity"] = "/private/tmp/producer/libaeneas_AeneasMeta.dylib"
        with patch.object(publisher, "_tool", return_value=""):
            with self.assertRaisesRegex(ValueError, "non-relocatable"):
                publisher.loader_closure(self.root, plugin, self.platform, relocate=True)


if __name__ == "__main__":
    unittest.main()
