# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Exercise archive identity, CLI provenance, and the Nix-free cache path."""
import importlib.util
import json
import os
import shlex
import shutil
import sys
import tarfile
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('aeneas_toolchain', ROOT / 'verification/aeneas/toolchain.py')
toolchain = importlib.util.module_from_spec(spec)
spec.loader.exec_module(toolchain)


def restore_script():
    script = (ROOT / 'verification/aeneas/negative-control-family.sh').read_text()
    return script.split("<<'PYRESTORE'\n", 1)[1].split('\nPYRESTORE', 1)[0]


class InstalledToolchainTests(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory(prefix='aeneas-toolchain-test-')
        self.addCleanup(self.scratch.cleanup)
        self.tools = Path(self.scratch.name) / 'tools with spaces'
        self.tools.mkdir()
        lock = json.loads((ROOT / 'anneal/flake.lock').read_text())
        nodes = lock['nodes']
        aeneas = nodes[nodes[lock['root']]['inputs']['aeneas']]
        charon = nodes[aeneas['inputs']['charon']]
        # Synthetic runtime versions avoid embedding a second upstream pin.
        self.data = {'aeneas-release': 'nightly-2099.01.01-' + aeneas['locked']['rev'][:7],
                     'aeneas-revision': aeneas['locked']['rev'],
                     'aeneas-source-nar-hash': aeneas['locked']['narHash'],
                     'charon-revision': charon['locked']['rev'],
                     'lean-toolchain': '9.0.0', 'rust-toolchain-date': '2099-01-01',
                     'rust-toolchain-version': 'nightly-2099-01-01'}
        self.metadata = self.tools / 'bundle/aeneas/metadata.json'
        self.metadata.parent.mkdir(parents=True)
        self.metadata.write_text(json.dumps(self.data))
        backend = self.tools / 'backends/lean/lean-toolchain'
        backend.parent.mkdir(parents=True)
        backend.write_text('leanprover/lean4:v9.0.0\n')
        self.executable('aeneas', 'echo "aeneas ' + self.data['aeneas-release'] + toolchain.PATCH_SUFFIX + '"')
        self.executable('aeneas-upstream', 'echo "aeneas ' + self.data['aeneas-release'] + '"')
        self.executable('charon', 'if [ "$1" = version ]; then echo "0.0.1 (' + self.data['charon-revision'] + ')"; else echo nightly-2099-01-01; fi')
        self.executable('charon-driver', 'exit 0')
        self.executable('rust/bin/rustc', 'echo "rustc 9.0.0-nightly (abcdef000 2098-12-31)"')
        self.executable('rust/bin/cargo', 'echo fake-cargo')
        self.executable('lean/bin/lean', 'echo "Lean (version 9.0.0, fake-platform, Release)"')
        self.executable('lean/bin/lake', 'exit 0')
        self.record()

    def executable(self, name, body):
        path = self.tools / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text('#!/bin/sh\n' + body + '\n')
        path.chmod(0o755)

    def record(self):
        (self.tools / 'aeneas-build.json').write_text(json.dumps(toolchain.provenance(self.tools, self.data)))

    def test_valid_cache_does_not_invoke_nix(self):
        marker = self.tools / 'nix-was-called'
        self.executable('nix', 'touch "' + str(marker) + '"; exit 91')
        result = subprocess.run(['bash', 'verification/aeneas/setup.sh'], cwd=ROOT,
                                env=dict(os.environ, AENEAS_TOOLCHAIN_DIR=str(self.tools),
                                         PATH=str(self.tools) + os.pathsep + os.environ['PATH']),
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('Using validated Anneal toolchain', result.stdout)
        self.assertFalse(marker.exists())

    def modern_record(self):
        (self.tools / 'aeneas-build.json').write_text(json.dumps(toolchain.provenance(self.tools, self.data, ROOT)))

    def test_shared_cache_reuses_validated_installation_without_nix(self):
        self.modern_record()
        cache = Path(self.scratch.name) / 'cache'
        cache.mkdir()
        entry = cache / toolchain.cache_key(ROOT)
        self.tools.rename(entry)
        self.tools = entry
        adapter = Path(self.scratch.name) / 'adapter'
        fake = Path(self.scratch.name) / 'fake-bin'
        fake.mkdir()
        nix = fake / 'nix'
        nix.write_text('#!/bin/sh\nexit 91\n')
        nix.chmod(0o755)
        result = subprocess.run(['bash', 'verification/aeneas/setup.sh'], cwd=ROOT,
                                env=dict(os.environ, AENEAS_TOOLCHAIN_DIR=str(adapter),
                                         AENEAS_TOOLCHAIN_CACHE_DIR=str(cache),
                                         PATH=str(fake) + os.pathsep + os.environ['PATH']),
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(adapter.is_symlink())
        self.assertEqual(adapter.resolve(), entry.resolve())
        toolchain.validate(ROOT, entry, cache=True)

    def test_shared_cache_rejects_legacy_provenance(self):
        with self.assertRaisesRegex(ValueError, 'Shared cache requires'):
            toolchain.validate(ROOT, self.tools, cache=True)
        toolchain.validate(ROOT, self.tools)

    def test_modern_record_checks_library_and_lean_artifact_bytes(self):
        for name in ['rust/lib/libcompiler.so', 'backends/lean/.lake/build/lib/lean/Model.olean']:
            path = self.tools / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b'original')
        self.modern_record()
        for name in ['rust/lib/libcompiler.so', 'backends/lean/.lake/build/lib/lean/Model.olean']:
            path = self.tools / name
            path.write_bytes(b'mutated')
            with self.assertRaisesRegex(ValueError, 'provenance mismatch'):
                toolchain.validate(ROOT, self.tools, cache=True)
            path.write_bytes(b'original')
        toolchain.validate(ROOT, self.tools, cache=True)

    def test_cache_identity_invalidates_builder_archive_and_patch_changes(self):
        clone = Path(self.scratch.name) / 'producer'
        identity = toolchain.build_identity(ROOT)
        for name in identity['inputs']:
            target = clone / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / name, target)
        key = toolchain.cache_key(clone)
        self.assertEqual(key, toolchain.cache_key(ROOT))
        for name in ['anneal/flake.lock', 'anneal/flake.nix', 'anneal/lean/Rust.lean',
                     'verification/aeneas/build-aeneas.nix']:
            target = clone / name
            original = target.read_bytes()
            target.write_bytes(original + b'\n')
            self.assertNotEqual(key, toolchain.cache_key(clone), name)
            target.write_bytes(original)

    def test_cache_key_ignores_generated_companion_manifest_only(self):
        clone = Path(self.scratch.name) / 'producer'
        for name in toolchain.build_identity(ROOT)['inputs']:
            target = clone / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / name, target)
        expected = toolchain.cache_key(clone)
        generated = clone / 'anneal/lean/aeneas/lake-manifest.json'
        generated.parent.mkdir(parents=True, exist_ok=True)
        for checkout in ['/first/checkout', '/different/checkout']:
            generated.write_text(json.dumps({'packages': [{'dir': checkout}]}))
            self.assertEqual(toolchain.cache_key(clone), expected)
        generated.unlink()
        self.assertEqual(toolchain.cache_key(clone), expected)
        for name in ['anneal/lean/lake-manifest.json', 'anneal/lean/Rust.lean']:
            authored = clone / name
            original = authored.read_bytes()
            authored.write_bytes(original + b'\n')
            self.assertNotEqual(toolchain.cache_key(clone), expected, name)
            authored.write_bytes(original)

    def test_modern_payload_rejects_external_symlink(self):
        outside = Path(self.scratch.name) / 'outside-library'
        outside.write_bytes(b'library')
        (self.tools / 'external').symlink_to(outside)
        with self.assertRaisesRegex(ValueError, 'symlink leaves installation'):
            self.modern_record()

    def test_cache_lock_is_not_stolen(self):
        cache = Path(self.scratch.name) / 'cache'
        cache.mkdir()
        lock = cache / ('.' + toolchain.cache_key(ROOT) + '.lock')
        lock.mkdir()
        adapter = Path(self.scratch.name) / 'adapter'
        result = subprocess.run(['bash', 'verification/aeneas/setup.sh'], cwd=ROOT,
                                env=dict(os.environ, AENEAS_TOOLCHAIN_DIR=str(adapter),
                                         AENEAS_TOOLCHAIN_CACHE_DIR=str(cache)),
                                capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('cache is locked', result.stderr)
        self.assertTrue(lock.is_dir())
        self.assertFalse(adapter.exists())

    def test_native_publication_refuses_existing_destinations(self):
        for kind in ['empty-directory', 'nonempty-directory', 'file', 'symlink']:
            with self.subTest(kind=kind):
                base = Path(self.scratch.name) / kind
                base.mkdir()
                source, destination = base / 'staged', base / 'destination'
                source.mkdir()
                (source / 'marker').write_text('new installation')
                if kind in ['empty-directory', 'nonempty-directory']:
                    destination.mkdir()
                    if kind == 'nonempty-directory':
                        (destination / 'marker').write_text('existing installation')
                elif kind == 'file':
                    destination.write_text('existing file')
                else:
                    destination.symlink_to('absent')
                before = destination.lstat()
                with self.assertRaises(OSError):
                    toolchain.publish_installation(source, destination)
                self.assertEqual(destination.lstat().st_ino, before.st_ino)
                self.assertEqual((source / 'marker').read_text(), 'new installation')
                if kind == 'empty-directory':
                    self.assertEqual(list(destination.iterdir()), [])
                elif kind == 'nonempty-directory':
                    self.assertEqual((destination / 'marker').read_text(), 'existing installation')
                elif kind == 'file':
                    self.assertEqual(destination.read_text(), 'existing file')
                else:
                    self.assertEqual(os.readlink(destination), 'absent')

    def test_native_publication_allows_exactly_one_concurrent_producer(self):
        base = Path(self.scratch.name) / 'producers'
        base.mkdir()
        destination = base / 'installed'
        sources = [base / 'first', base / 'second']
        processes = []
        for source in sources:
            source.mkdir()
            (source / 'marker').write_text(source.name)
            processes.append(subprocess.Popen([sys.executable, '-B',
                str(ROOT / 'verification/aeneas/toolchain.py'), 'publish', str(source), str(destination)],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True))
        results = [process.communicate(timeout=10) for process in processes]
        self.assertEqual(sorted(process.returncode for process in processes), [0, 1], results)
        winner = (destination / 'marker').read_text()
        for source, process in zip(sources, processes):
            if process.returncode == 0:
                self.assertEqual(source.name, winner)
                self.assertFalse(source.exists())
            else:
                self.assertEqual((source / 'marker').read_text(), source.name)
        self.assertEqual(list(destination.iterdir()), [destination / 'marker'])

    def test_cold_setup_uses_anneal_archive_and_configured_source(self):
        scratch = Path(self.scratch.name)
        fake = scratch / 'fake-nix'
        fake.mkdir()
        source = scratch / 'upstream-source'
        (source / 'src').mkdir(parents=True)
        patch = (ROOT / 'verification/aeneas/patches/use-tuple-structs.patch').read_text()
        old_lines = [line[1:] for line in patch.splitlines() if line.startswith(' ') or
                     (line.startswith('-') and not line.startswith('---'))]
        (source / 'src/Main.ml').write_text('\n'.join(old_lines) + '\n')
        self.executable('bundle/aeneas/bin/aeneas', 'echo "aeneas ' + self.data['aeneas-release'] + '"')
        for name in ['charon', 'charon-driver']:
            target = self.tools / ('bundle/aeneas/bin/' + name)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((self.tools / name).read_bytes())
            target.chmod(0o755)
        # Darwin bundles and their private adapter copies can have read-only
        # libraries. The patched CLI must replace its own copy, while leaving
        # the producer's copy intact. Freeze archive directories too: an abort
        # must still remove its private staging directory.
        upstream_library = self.tools / 'bundle/aeneas/bin/libs/libgmp.10.dylib'
        upstream_library.parent.mkdir()
        upstream_library.write_bytes(b'upstream library')
        upstream_library.chmod(0o444)
        # A tiny archive stands in for the validated producer payload; only the
        # orchestration is under test, not Nix compilation or compression.
        archive = scratch / 'bundle.tar'
        def frozen_directories(member):
            if member.isdir():
                member.mode &= ~0o222
            return member
        with tarfile.open(archive, 'w') as tar:
            for name in ['bundle/aeneas', 'rust', 'lean']:
                tar.add(self.tools / name, arcname=name.removeprefix('bundle/'), filter=frozen_directories)
            tar.add(self.tools / 'backends', arcname='aeneas/backends', filter=frozen_directories)
        extractor = scratch / 'extractor/bin'
        extractor.mkdir(parents=True)
        tar_script = extractor / 'tar'
        tar_script.write_text('#!' + sys.executable + '\nimport sys,tarfile\na=sys.argv\ntarfile.open(a[a.index("-xf")+1]).extractall(a[a.index("-C")+1])\n')
        tar_script.chmod(0o755)
        artifact = scratch / 'patched-cli'
        artifact.mkdir()
        binary = artifact / 'aeneas'
        binary.write_text('#!/bin/sh\nif [ "$1" = -help ]; then echo -use-tuple-structs; else echo "aeneas ' + self.data['aeneas-release'] + toolchain.PATCH_SUFFIX + '"; fi\n')
        binary.chmod(0o755)
        patched_library = artifact / 'libs/libgmp.10.dylib'
        patched_library.parent.mkdir()
        patched_library.write_bytes(b'patched library')
        patched_library.chmod(0o444)
        nix = fake / 'nix'
        nix.write_text('#!' + sys.executable + '\n' +
                       'import os,sys,json\nfrom pathlib import Path\na=" ".join(sys.argv[1:])\n' +
                       'if "builtins.currentSystem" in a: print("x86_64-linux")\n' +
                       'elif "toolchain.aeneas-source" in a: print(' + repr(str(source)) + ')\n' +
                       'elif "--json" in a and ".toolchain" in a: print(' + repr(json.dumps(self.data)) + ')\n' +
                       'elif "#omnibus-archive-ci" in a: print(' + repr(str(archive)) + ')\n' +
                       'elif "#omnibus-archive-layout-check" in a: pass\n' +
                       'elif ".gnutar" in a or ".zstd.bin" in a: print(' + repr(str(extractor.parent)) + ')\n' +
                       'elif "build-aeneas.nix" in a:\n' +
                       ' assert "-use-tuple-structs" in (Path(os.environ["AENEAS_SOURCE_DIR"])/"src/Main.ml").read_text()\n' +
                       ' assert Path(os.environ["ANNEAL_FLAKE_DIR"]).name=="anneal"\n' +
                       ' print(' + repr(str(artifact)) + ')\n' +
                       'else: raise SystemExit("Unexpected Nix call: "+a)\n')
        nix.chmod(0o755)
        installation = scratch / 'cold-install'
        result = subprocess.run(['bash', 'verification/aeneas/setup.sh'], cwd=ROOT,
                                env=dict(os.environ, AENEAS_TOOLCHAIN_DIR=str(installation),
                                         PATH=str(fake) + os.pathsep + os.environ['PATH']),
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        toolchain.validate(ROOT, installation)
        self.assertEqual((installation / 'bundle/aeneas/metadata.json').read_bytes(), self.metadata.read_bytes())
        self.assertTrue((installation / 'backends').is_symlink())
        self.assertFalse((installation / 'aeneas').is_symlink())
        self.assertEqual((installation / 'libs/libgmp.10.dylib').read_bytes(), b'patched library')
        self.assertEqual((installation / 'bundle/aeneas/bin/libs/libgmp.10.dylib').read_bytes(), b'upstream library')
        self.assertNotIn('-use-tuple-structs', (source / 'src/Main.ml').read_text())
        # The destination can appear after setup's initial observation. The
        # native publication boundary must retain both the existing directory
        # and the validated stage, rather than nesting the stage inside it.
        collision = scratch / 'collision-install'
        original_nix = nix.read_text()
        publish_line = ' print(' + repr(str(artifact)) + ')\n'
        collision_lines = (' collision = Path(' + repr(str(collision)) + ')\n'
                           ' collision.mkdir()\n'
                           ' (collision/"existing").write_text("preserved")\n' + publish_line)
        self.assertIn(publish_line, original_nix)
        nix.write_text(original_nix.replace(publish_line, collision_lines))
        raced = subprocess.run(['bash', 'verification/aeneas/setup.sh'], cwd=ROOT,
                               env=dict(os.environ, AENEAS_TOOLCHAIN_DIR=str(collision),
                                        PATH=str(fake) + os.pathsep + os.environ['PATH']),
                               capture_output=True, text=True)
        self.assertNotEqual(raced.returncode, 0)
        self.assertIn('Publication rejected', raced.stderr)
        self.assertEqual(list(collision.iterdir()), [collision / 'existing'])
        self.assertEqual((collision / 'existing').read_text(), 'preserved')
        retained = list(scratch.glob('setup.*'))
        self.assertEqual(len(retained), 1)
        toolchain.validate(ROOT, retained[0] / 'toolchain', cache=True)
        for directory, _, _ in os.walk(retained[0], followlinks=False):
            path = Path(directory)
            path.chmod(path.stat().st_mode | 0o200)
        shutil.rmtree(retained[0])
        nix.write_text(original_nix)
        wrong = dict(self.data, **{'aeneas-source-nar-hash': 'wrong'})
        nix.write_text(nix.read_text().replace(repr(json.dumps(self.data)), repr(json.dumps(wrong))))
        rejected = scratch / 'rejected-install'
        failed = subprocess.run(['bash', 'verification/aeneas/setup.sh'], cwd=ROOT,
                                env=dict(os.environ, AENEAS_TOOLCHAIN_DIR=str(rejected),
                                         PATH=str(fake) + os.pathsep + os.environ['PATH']),
                                capture_output=True, text=True)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn('archive metadata mismatch', failed.stderr)
        self.assertFalse(rejected.exists())
        self.assertFalse(list(scratch.glob('setup.*')), 'Failed setup left its read-only staging directory')
        toolchain.validate(ROOT, installation)

    def test_shell_exports_archive_cargo_and_versions(self):
        result = subprocess.run(['bash', '-c', 'source verification/aeneas/toolchain.sh && command -v cargo && printf "%s\\n" "$AENEAS_RUST_TOOLCHAIN"'],
                                cwd=ROOT, env=dict(os.environ, AENEAS_TOOLCHAIN_DIR=str(self.tools)),
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(), [str(self.tools / 'rust/bin/cargo'), 'nightly-2099-01-01'])

    def test_shell_lake_policy_preserves_ci_and_failure_status(self):
        for status in (0, 19):
            with self.subTest(status=status):
                self.executable('lean/bin/lake',
                                'test "${CI+x}" != x || exit 98\n' +
                                'printf "%s\\n" "$@"\nexit ' + str(status))
                self.record()
                result = subprocess.run(
                    ['bash', '-c', 'source verification/aeneas/toolchain.sh || exit; aeneas_lake build Required; status=$?; printf "CI=%s\\n" "$CI"; exit "$status"'],
                    cwd=ROOT, env=dict(os.environ, CI='true', AENEAS_TOOLCHAIN_DIR=str(self.tools)),
                    capture_output=True, text=True)
                self.assertEqual(result.returncode, status, result.stderr)
                self.assertEqual(result.stdout.splitlines(), ['--old', 'build', 'Required', 'CI=true'])

    def test_failure_controls_use_shared_lake_policy(self):
        script = (ROOT / 'verification/aeneas/negative-control-family.sh').read_text()
        for line in script.splitlines():
            if not line.lstrip().startswith('#'):
                self.assertNotRegex(line, r'\blake\s+(?:build|env)\b')
        self.assertIn('aeneas_lake build Required', script)
        self.assertIn('aeneas_lake env lean', script)

    def test_failure_controls_restore_all_sources_for_lake_old_mode(self):
        body = restore_script()
        project = Path(self.scratch.name) / 'restoration'
        backup = project / 'backup'
        backup.mkdir(parents=True)
        for name in ['Keep.lean', 'Changed.lean', 'Missing.lean', 'bindings.json']:
            (backup / name).write_text('baseline')
            if name != 'Missing.lean':
                (project / name).write_text('changed' if name == 'Changed.lean' else 'baseline')
                os.utime(project / name, ns=(1_000_000_000, 1_000_000_000))
        result = subprocess.run([sys.executable, '-c', body, str(backup)],
                                cwd=project, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        for name in ['Keep.lean', 'Changed.lean', 'Missing.lean', 'bindings.json']:
            self.assertEqual((project / name).read_text(), 'baseline')
        # Restore byte-identical inputs without copying them again. Semantic
        # proof builds discard mutable outputs independently of these times.
        for name in ['Keep.lean', 'bindings.json']:
            self.assertEqual((project / name).stat().st_mtime_ns, 1_000_000_000)
        self.assertGreater((project / 'Changed.lean').stat().st_mtime_ns, 1_000_000_000)

    def test_restored_proof_is_checked_against_restored_model(self):
        lake = shutil.which('lake')
        if lake is None:
            self.skipTest('Requires the pinned Lean installation')
        project = Path(self.scratch.name) / 'proof cache'
        project.mkdir()
        (project / 'lean-toolchain').write_bytes((ROOT / 'anneal/lean/lean-toolchain').read_bytes())
        (project / 'lakefile.lean').write_text(
            'import Lake\nopen Lake DSL\npackage cache_test\n'
            '@[default_target] lean_lib Model\n@[default_target] lean_lib Proof\n')
        model = project / 'Model.lean'
        model.write_text('def modeled : Nat := 1\n')
        proof = project / 'Proof.lean'
        proof.write_text('import Model\ntheorem modeled_spec : modeled = 1 := by rfl\n')
        (project / 'bindings.json').write_text('{}\n')
        env = dict(os.environ)
        env.pop('CI', None)

        def run(args):
            return subprocess.run(args, cwd=project, env=env, capture_output=True,
                                  text=True, timeout=60)

        baseline = run([lake, '--old', 'build'])
        self.assertEqual(baseline.returncode, 0, baseline.stdout + baseline.stderr)
        # Keep a proof compiled against model 1, then restore model 2 alongside
        # the identical proof source. Restoring bytes alone must not be treated
        # as proof validation: --old can still reuse the unchanged proof.
        proof_time = proof.stat().st_mtime_ns
        backup = project / 'backup'
        backup.mkdir()
        for name in ['Model.lean', 'Proof.lean', 'bindings.json']:
            shutil.copyfile(project / name, backup / name)
        (backup / 'Model.lean').write_text('def modeled : Nat := 2\n')
        restored = run([sys.executable, '-c', restore_script(), str(backup)])
        self.assertEqual(restored.returncode, 0, restored.stderr)
        mutant = run([lake, '--old', 'build', '+Model'])
        self.assertEqual(mutant.returncode, 0, mutant.stdout + mutant.stderr)
        self.assertEqual(proof.stat().st_mtime_ns, proof_time)
        stale = run([lake, '--old', 'build', 'Proof'])
        self.assertEqual(stale.returncode, 0, stale.stdout + stale.stderr)
        rejected = run([sys.executable, '-B',
            str(ROOT / 'verification/aeneas/control_runner.py'), 'command', '--fresh',
            str(project / 'logs'), '--', lake, '--old', 'build', 'Proof'])
        self.assertNotEqual(rejected.returncode, 0)
        self.assertIn('rfl', rejected.stdout + rejected.stderr)

    def test_full_source_identity_mismatch_rejected_without_metadata_repair(self):
        for key in ['aeneas-revision', 'aeneas-source-nar-hash', 'charon-revision']:
            with self.subTest(key=key):
                changed = dict(self.data, **{key: 'wrong'})
                self.metadata.write_text(json.dumps(changed))
                original = self.metadata.read_bytes()
                with self.assertRaisesRegex(ValueError, 'identity mismatch'):
                    toolchain.validate(ROOT, self.tools)
                self.assertEqual(original, self.metadata.read_bytes())

    def test_binary_mutation_rejected(self):
        self.executable('aeneas', 'echo "aeneas wrong-version"')
        with self.assertRaisesRegex(ValueError, 'provenance mismatch'):
            toolchain.validate(ROOT, self.tools)

    def test_metadata_version_mutation_rejected(self):
        self.metadata.write_text(json.dumps(dict(self.data, **{'lean-toolchain': '9.0.1'})))
        with self.assertRaisesRegex(ValueError, 'provenance mismatch'):
            toolchain.validate(ROOT, self.tools)

    def test_coherent_wrong_cli_version_still_rejected(self):
        self.executable('aeneas', 'echo "aeneas wrong-version"')
        self.record()
        with self.assertRaisesRegex(ValueError, 'version mismatch'):
            toolchain.validate(ROOT, self.tools)

    def test_wrong_charon_revision_still_rejected(self):
        self.executable('charon', 'echo "0.0.1 (wrong-revision)"')
        self.record()
        with self.assertRaisesRegex(ValueError, 'Charon revision mismatch'):
            toolchain.validate(ROOT, self.tools)

    def test_missing_provenance_fails_closed(self):
        (self.tools / 'aeneas-build.json').unlink()
        with self.assertRaises(FileNotFoundError):
            toolchain.validate(ROOT, self.tools)

    def test_record_command_refuses_to_repair_existing_provenance(self):
        record = self.tools / 'aeneas-build.json'
        original = record.read_bytes()
        result = subprocess.run([sys.executable, '-B', 'verification/aeneas/toolchain.py', 'record', str(self.tools)],
                                cwd=ROOT, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Refusing to overwrite', result.stderr)
        self.assertEqual(record.read_bytes(), original)

    def test_record_refuses_dangling_symlink_without_creating_target(self):
        record = self.tools / 'aeneas-build.json'
        record.unlink()
        outside = Path(self.scratch.name) / 'outside-record'
        record.symlink_to(outside)
        result = subprocess.run([sys.executable, '-B', 'verification/aeneas/toolchain.py', 'record', str(self.tools)],
                                cwd=ROOT, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Refusing to overwrite', result.stderr)
        self.assertTrue(record.is_symlink())
        self.assertFalse(outside.exists())

    def test_source_build_short_revision_is_allowed_only_upstream(self):
        self.executable('aeneas', 'echo "aeneas ' + self.data['aeneas-revision'][:7] + '"')
        toolchain.validate(ROOT, self.tools, patched=False)
        self.record()
        with self.assertRaisesRegex(ValueError, 'Aeneas version mismatch'):
            toolchain.validate(ROOT, self.tools)


if __name__ == '__main__':
    unittest.main()
