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
    # Producer fixture follows the independently checked RC2 source format,
    # rather than manufacturing whatever files the publisher happens to demand.
    families = ("olean", "ilean", "olean.private", "olean.server", "ir") if split else ("olean", "ilean")
    for family in families:
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
        self.case = Path(tempfile.mkdtemp(prefix=self._testMethodName + "-", dir=scratch)).resolve()
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
        for name in ("lean", "lake", "leanc"):
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

    def finite_catalog(self):
        write(self.runtime / "bin/anneal-finite-lake", native(self.platform, b"finite producer"))
        (self.runtime / "bin/anneal-finite-lake").chmod(0o755)
        write(self.runtime / "src/anneal/FiniteLake.lean", "-- status-only helper source\n")
        write(self.runtime / "src/anneal/build-finite-lake.py", "# coherent producer recipe\n")
        # The ordinary runtime capture precedes the new trusted staged helper.
        # Remove its entry here to model catalog-finite extending that capture.
        catalog = self.catalog()
        catalog["runtime_inventory"].pop("bin/anneal-finite-lake")
        return publisher.catalog_finite(self.root, catalog)

    def support_catalog(self):
        catalog = self.catalog()
        module(self.runtime, "AnnealSupport", runtime=True)
        write(self.runtime / "src/anneal/build-anneal-support.py", "# exact support recipe\n")
        return publisher.catalog_support(self.root, catalog)

    def test_support_is_an_exact_unified_module_with_source_and_complete_family(self):
        catalog = self.support_catalog()
        descriptor = publisher.assemble(self.root, catalog)
        sdk = self.root / "lean-sdk"
        self.assertEqual(descriptor["schema"], 1)  # No new support capability flag.
        modules = json.loads((sdk / "modules.json").read_text())
        self.assertEqual(modules["schema"], 1)
        self.assertIn("AnnealSupport", modules["modules"])
        self.assertEqual((sdk / "src/lean/AnnealSupport.lean").read_bytes(),
                         (self.runtime / "src/lean/AnnealSupport.lean").read_bytes())
        for suffix in publisher.LEGACY:
            self.assertEqual((sdk / "lib/lean" / ("AnnealSupport." + suffix)).read_bytes(),
                             (self.runtime / "lib/lean" / ("AnnealSupport." + suffix)).read_bytes())
        content = json.loads((sdk / "publisher-catalog.json").read_text())["published"]
        self.assertEqual(content["anneal_support_producer"], catalog["anneal_support"])
        self.assertEqual(content["modules"]["AnnealSupport"]["provider"], "lean")

    def test_support_drift_or_incomplete_family_rejected_before_sdk_creation(self):
        catalog = self.support_catalog()
        for relative in ["src/lean/AnnealSupport.lean", "src/anneal/build-anneal-support.py",
                         "lib/lean/AnnealSupport.olean", "lib/lean/AnnealSupport.ilean"]:
            with self.subTest(relative=relative):
                path = self.runtime / relative
                original = path.read_bytes()
                path.write_bytes(original + b"changed")
                self.reject_assembly(catalog)
                path.write_bytes(original)
        for suffix in publisher.LEGACY:
            with self.subTest(suffix=suffix):
                changed = copy.deepcopy(catalog)
                del changed["modules"]["AnnealSupport"]["artifacts"][suffix]
                self.reject_assembly(changed)
        changed = copy.deepcopy(catalog)
        changed["runtime_inventory"]["lib/lean/AnnealSupport.olean"]["publisher_relocation"] = True
        self.reject_assembly(changed)
        changed = copy.deepcopy(catalog)
        changed["anneal_support"]["unknown"] = True
        self.reject_assembly(changed)

    def test_support_capture_cannot_adopt_existing_catalog_or_split_source(self):
        catalog = self.support_catalog()
        with self.assertRaises(ValueError):
            publisher.catalog_support(self.root, catalog)
        original = self.catalog()
        original["modules"].pop("AnnealSupport")
        original["runtime_inventory"].pop("lib/lean/AnnealSupport.olean")
        original["runtime_inventory"].pop("lib/lean/AnnealSupport.ilean")
        write(self.runtime / "src/lean/AnnealSupport.lean", "module\n-- changed source format\n")
        with self.assertRaises(ValueError):
            publisher.catalog_support(self.root, original)

    def test_finite_descriptor_keeps_module_map_schema_and_real_relocatable_helper(self):
        catalog = self.finite_catalog()
        # The helper's Lake closure is actually included rather than presumed
        # from an existing Lean/Lake launcher or only its executable hash.
        write(self.runtime / "lib/lean/libLake_shared.dylib", native())
        catalog["runtime_inventory"]["lib/lean/libLake_shared.dylib"] = {
            "sha256": publisher.digest(self.runtime / "lib/lean/libLake_shared.dylib"),
            "publisher_relocation": True}
        self.dependencies["anneal-finite-lake"] = {"needed":["@rpath/libLake_shared.dylib"],
            "rpaths":["@executable_path/../lib/lean"], "identity":None, "interpreter":"/usr/lib/dyld"}
        result = publisher.assemble(self.root, catalog)
        sdk = self.root / "lean-sdk"
        self.assertEqual(result["schema"], 2)
        self.assertEqual(result["finite_lake"], {"path":"bin/anneal-finite-lake",
            "sha256":publisher.digest(sdk / "bin/anneal-finite-lake"), "protocol":1})
        self.assertFalse((sdk / "bin/anneal-finite-lake").is_symlink())
        self.assertEqual(json.loads((sdk / "modules.json").read_text())["schema"], 1)
        content = json.loads((sdk / "publisher-catalog.json").read_text())["published"]
        self.assertIn("lean/bin/anneal-finite-lake", content["native_closure"]["images"])
        self.assertIn("lean/lib/lean/libLake_shared.dylib", content["native_closure"]["images"])
        self.assertEqual(content["finite_lake_producer"]["source"], catalog["finite_lake"]["source"])
        self.assertEqual(content["finite_lake_producer"]["recipe"], catalog["finite_lake"]["recipe"])

    def test_finite_source_recipe_and_runtime_provider_drift_reject_before_assembly(self):
        catalog = self.finite_catalog()
        for name in ["src/anneal/FiniteLake.lean", "src/anneal/build-finite-lake.py", "bin/anneal-finite-lake"]:
            path = self.runtime / name
            before = path.read_bytes()
            path.write_bytes(before + b"changed")
            self.reject_assembly(catalog)
            path.write_bytes(before)
        for change in [lambda c:c["finite_lake"].update(protocol=2),
                       lambda c:c["finite_lake"].update(protocol=True),
                       lambda c:c["finite_lake"].update(path="lean/bin/lake"),
                       lambda c:c["finite_lake"].update(unknown=1),
                       lambda c:c["runtime_inventory"].pop("bin/anneal-finite-lake")]:
            bad = copy.deepcopy(catalog)
            change(bad)
            self.reject_assembly(bad)

    def test_finite_final_relocation_bytes_enter_identity(self):
        catalog = self.finite_catalog()
        helper = self.runtime / "bin/anneal-finite-lake"
        helper.write_bytes(native(self.platform, b"relocated finite producer"))
        self.reject_assembly(catalog)
        result = publisher.assemble(self.root, catalog, allow_native_relocation=True)
        self.assertEqual(result["finite_lake"]["sha256"], publisher.digest(helper))
        self.assertNotEqual(result["finite_lake"]["sha256"], catalog["finite_lake"]["producer_sha256"])

    def test_finite_missing_lake_provider_is_not_assumed_or_host_resolved(self):
        catalog = self.finite_catalog()
        self.dependencies["anneal-finite-lake"] = {"needed":["@rpath/libLake_shared.dylib"],
            "rpaths":[], "identity":None, "interpreter":None}
        self.reject_assembly(catalog)

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

    def test_leanc_is_a_required_physical_executable_before_capture_and_assembly(self):
        catalog = self.catalog()
        path = self.runtime / "bin/leanc"
        original = path.read_bytes()
        for failure in ("missing", "linked", "non-executable", "wrong-architecture"):
            with self.subTest(failure=failure):
                if path.exists() or path.is_symlink():
                    path.unlink()
                write(path, original)
                path.chmod(0o755)
                if failure == "missing":
                    path.unlink()
                elif failure == "linked":
                    path.unlink()
                    path.symlink_to("lean")
                elif failure == "non-executable":
                    path.chmod(0o644)
                else:
                    write(path, native("x86_64-darwin"))
                with self.assertRaises((ValueError, FileNotFoundError)):
                    self.catalog()
                self.reject_assembly(catalog)

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

    def test_split_package_ir_is_pinned_and_published_without_unproduced_signature(self):
        module(self.project, "Aeneas.Split", split=True)
        catalog = self.catalog()
        ir = self.project / ".lake/build/lib/lean/Aeneas/Split.ir"
        self.assertEqual(catalog["modules"]["Aeneas.Split"]["artifacts"]["ir"]["sha256"], publisher.digest(ir))
        original = ir.read_bytes()
        write(ir, olean(b"changed IR"))
        self.reject_assembly(catalog)
        ir.write_bytes(original)
        publisher.assemble(self.root, catalog)
        self.assertEqual((self.root / "lean-sdk/lib/lean/Aeneas/Split.ir").resolve(), ir)
        self.assertFalse((self.root / "lean-sdk/lib/lean/Aeneas/Split.ir.sig").exists())

    def test_root_mathlib_mirror_cannot_claim_canonical_package_exports(self):
        module(self.packages / "mathlib", "Mathlib.Keep", split=True)
        module(self.packages / "mathlib", "Mathlib.Drop", split=True)
        canonical = self.catalog({"Mathlib.Keep"})
        root_lib = self.project / ".lake/build/lib/lean"
        package_lib = self.packages / "mathlib/.lake/build/lib/lean"
        # Reproduce the root-level files handled by prune_root_mathlib_cache,
        # including an orphan companion whose source is only in the package.
        shutil.copytree(package_lib / "Mathlib", root_lib / "Mathlib")
        write(root_lib / "Mathlib.olean", olean(b"mirrored umbrella"))
        write(root_lib / "Mathlib.ilean", "{}\n")
        write(root_lib / "Mathlib/Orphan.ir", olean(b"unused mirrored IR"))
        mirrored = {str(p.relative_to(root_lib)): p.read_bytes()
                    for p in root_lib.rglob("*") if p.is_file() and p.relative_to(root_lib).parts[0].startswith("Mathlib")}
        catalog = self.catalog({"Mathlib.Keep"})
        self.assertEqual(catalog["modules"], canonical["modules"])
        self.assertEqual(catalog["modules"]["Mathlib.Keep"]["provider"], "mathlib")
        self.assertNotIn("Mathlib.Drop", catalog["modules"])
        self.assertNotIn("Mathlib", catalog["modules"])
        publisher.assemble(self.root, catalog)
        self.assertEqual((self.root / "lean-sdk/lib/lean/Mathlib/Keep.ir").resolve(), package_lib / "Mathlib/Keep.ir")
        for relative, contents in mirrored.items():
            self.assertEqual((root_lib / relative).read_bytes(), contents)
        (package_lib / "Mathlib/Keep.ir").unlink()
        with self.assertRaises(FileNotFoundError):
            self.catalog({"Mathlib.Keep"})  # The mirror cannot fill a canonical omission.

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
        for name in ("lean", "lake", "leanc"):
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

    def test_lazy_dylib_parser_reaches_recursive_admitted_native_providers(self):
        lazy = self.runtime / "lib/libLazy.dylib"
        write(lazy, native(payload=b"lazy provider"))
        self.dependencies["leanc"] = publisher.parse_native(
            "cmd LC_LAZY_LOAD_DYLIB\nname @rpath/libLazy.dylib (offset 24)\n", self.platform)
        self.dependencies["libLazy.dylib"] = publisher.parse_native(
            "cmd LC_LOAD_DYLIB\nname @rpath/libleanshared.dylib (offset 24)\n", self.platform)
        publisher.assemble(self.root, self.catalog())
        published = json.loads((self.root / "lean-sdk/publisher-catalog.json").read_text())["published"]
        images = published["native_closure"]["images"]
        self.assertEqual(images["lean/bin/leanc"]["loader"]["needed"], ["@rpath/libLazy.dylib"])
        self.assertIn("lean/lib/libLazy.dylib", images)
        self.assertIn("lean/lib/libleanshared.dylib", images)
        # Inspection must reject the missing lazy provider even though no eager
        # dependency from another consumed root demands that provider.
        lazy.unlink()
        plugin = self.project / ".lake/build/lib/libaeneas_AeneasMeta.dylib"
        with self.assertRaisesRegex(ValueError, "missing native dependency.*libLazy"):
            publisher.loader_closure(self.root, plugin, self.platform)

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
        # Neither Lean nor Lake reaches this private provider. Its admission
        # depends on walking the consumed native C-wrapper launcher as a root.
        write(self.runtime / "lib/libLeancOnly.dylib", native())
        self.dependencies["leanc"] = {"needed": ["@rpath/libLeancOnly.dylib"], "rpaths": ["@executable_path/../lib"], "identity": None, "interpreter": "/usr/lib/dyld"}
        self.dependencies["libLeancOnly.dylib"] = {"needed": ["@rpath/libleanshared.dylib"], "rpaths": [], "identity": "@rpath/libLeancOnly.dylib", "interpreter": None}
        result = publisher.assemble(self.root, self.catalog())
        published = json.loads((self.root / "lean-sdk/publisher-catalog.json").read_text())["published"]
        self.assertIn("lean/lib/libleanshared.dylib", published["native_closure"]["images"])
        self.assertIn("lean/bin/leanc", published["native_closure"]["images"])
        self.assertIn("lean/lib/libLeancOnly.dylib", published["native_closure"]["images"])
        self.assertEqual((self.root / "lean-sdk/bin/leanc").resolve(), self.runtime / "bin/leanc")
        self.assertEqual(published["native_closure"]["system"], ["/usr/lib/libSystem.B.dylib"])
        self.assertIn("../aeneas/backends/lean/.lake/build/lib", result["loader_roots"])

    def test_linux_loader_dependency_is_an_exact_platform_assumption(self):
        plugin = self.project / ".lake/build/lib/libaeneas_AeneasMeta.so"
        for platform, interpreter in (("x86_64-linux", "/lib64/ld-linux-x86-64.so.2"),
                                      ("aarch64-linux", "/lib/ld-linux-aarch64.so.1")):
            with self.subTest(platform=platform):
                for name in ("lean", "lake", "leanc"):
                    write(self.runtime / "bin" / name, native(platform))
                write(plugin, native(platform))
                loader = Path(interpreter).name
                self.dependencies["lean"] = {"needed": [loader], "rpaths": [], "identity": None,
                                             "interpreter": interpreter}
                result = publisher.loader_closure(self.root, plugin, platform)
                self.assertEqual(result["system"], [loader])
                self.dependencies["lean"]["needed"] = [interpreter]
                result = publisher.loader_closure(self.root, plugin, platform)
                self.assertEqual(result["system"], [interpreter])
                other = "/lib/ld-linux-aarch64.so.1" if platform == "x86_64-linux" else "/lib64/ld-linux-x86-64.so.2"
                for dependency in (other, Path(other).name, "/nix/store/glibc/" + loader, "ld-unknown.so.1"):
                    self.dependencies["lean"]["needed"] = [dependency]
                    with self.assertRaisesRegex(ValueError, "native reference|native dependency"):
                        publisher.loader_closure(self.root, plugin, platform)
                self.dependencies["lean"]["needed"] = []
                self.dependencies["lean"]["interpreter"] = other
                with self.assertRaisesRegex(ValueError, "non-system native interpreter"):
                    publisher.loader_closure(self.root, plugin, platform)

    def test_missing_unaccounted_or_escaping_native_dependency_rejected(self):
        catalog = self.catalog()
        for name in ("lean", "lake", "leanc"):
            for reference in ("@rpath/libMissing.dylib", "/nix/store/package/libDependency.dylib", "../foreign.dylib"):
                with self.subTest(launcher=name, reference=reference):
                    self.dependencies.clear()
                    self.dependencies[name] = {"needed": [reference], "rpaths": [], "identity": None, "interpreter": None}
                    self.reject_assembly(catalog)
        self.dependencies.clear()
        self.dependencies["lean"] = {"needed": ["@rpath/libOther.dylib"], "rpaths": [], "identity": None, "interpreter": None}
        write(self.project / ".lake/build/lib/libOther.dylib", native())
        self.reject_assembly(catalog)  # Not recorded by trusted producer.

    def test_residual_native_rpath_identity_and_interpreter_rejected(self):
        catalog = self.catalog()
        for name in ("lean", "lake", "leanc"):
            for key, value in (("rpaths", ["/nix/store/lib"]), ("identity", "/private/tmp/producer/libSelf.dylib"),
                               ("interpreter", "/nix/store/glibc/ld.so")):
                with self.subTest(launcher=name, field=key):
                    self.dependencies.clear()
                    information = {"needed": [], "rpaths": [], "identity": None, "interpreter": None}
                    information[key] = value
                    self.dependencies[name] = information
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


        self.dependencies.clear()
        leanc = self.runtime / "bin/leanc"
        original_reference = str(self.runtime / "lib/libleanshared.dylib")
        original_rpath = str(self.runtime / "lib")
        information = {"needed": [original_reference], "rpaths": [original_rpath], "identity": None, "interpreter": "/usr/lib/dyld"}
        self.dependencies[leanc.name] = information
        def relocate_leanc(arguments):
            if arguments[0] == "codesign":
                self.assertIn("--timestamp=none", arguments)
                return ""
            self.assertEqual(arguments[-1], str(leanc))
            if arguments[1] == "-change":
                self.assertEqual(arguments[2], original_reference)
                information["needed"] = [arguments[3]]
            else:
                self.assertEqual(arguments[1:3], ["-delete_rpath", original_rpath])
                information["rpaths"] = []
            return ""
        with patch.object(publisher, "_tool", side_effect=relocate_leanc) as commands:
            closure = publisher.loader_closure(self.root, plugin, self.platform, relocate=True)
            self.assertEqual(commands.call_count, 3)
            self.assertEqual(closure["images"]["lean/bin/leanc"]["loader"]["needed"], ["@rpath/libleanshared.dylib"])
        information["needed"] = [original_reference]
        information["rpaths"] = [original_rpath]
        with patch.object(publisher, "_tool", return_value=""):
            with self.assertRaisesRegex(ValueError, "non-system absolute native"):
                publisher.loader_closure(self.root, plugin, self.platform, relocate=True)


if __name__ == "__main__":
    unittest.main()
