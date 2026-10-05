# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Tiny native-loader fixtures; Apple tools and native subjects never execute."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location('native_tools', Path(__file__).parents[1] / 'prepare-native-tools.py')
native = importlib.util.module_from_spec(spec)
spec.loader.exec_module(native)
ICONV = '/nix/store/example-libiconv-109/lib/libiconv.2.dylib'
ZLIB = '/nix/store/example-zlib-1.3.1/lib/libz.dylib'
DRIVER = 'librustc_driver-deadbeef.dylib'
SYSTEM = '/usr/lib/libSystem.B.dylib'


class NativeToolsTest(unittest.TestCase):
    def fixture(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        root = Path(temp.name).resolve()
        paths = {name: root / relative for name, relative in {
            'aeneas': 'aeneas/bin/aeneas', 'charon': 'aeneas/bin/charon',
            'charon-driver': 'aeneas/bin/charon-driver', 'gmp': 'aeneas/bin/libs/libgmp.10.dylib',
            'driver': 'rust/lib/' + DRIVER}.items()}
        for path in paths.values():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b'private fixture, never executed')
        dependencies = {
            paths['charon']: [ICONV, SYSTEM],
            paths['charon-driver']: ['@rpath/' + DRIVER, ICONV, ZLIB, SYSTEM],
            paths['aeneas']: ['@executable_path/libs/libgmp.10.dylib', SYSTEM],
            paths['gmp']: [SYSTEM], paths['driver']: [SYSTEM]}
        events = []
        def tool(name, *args):
            events.append((name, args))
            if name == 'otool':
                return ''.join('cmd LC_LOAD_DYLIB\nname ' + ref + ' (offset 24)\n' for ref in dependencies[args[-1]])
            if name == 'nm':
                return ''
            if name == 'lipo':
                return 'arm64'
            if name == 'install_name_tool':
                _, old, new, image = args
                dependencies[image] = [new if ref == old else ref for ref in dependencies[image]]
                return ''
            if name == 'codesign':
                return ''
            raise AssertionError('Unexpected static tool: ' + name)
        return root, paths, dependencies, events, tool

    def test_stage_changes_only_reviewed_commands_and_keeps_native_provider_bytes(self):
        root, paths, dependencies, events, tool = self.fixture()
        before = {name: path.read_bytes() for name, path in paths.items()}
        with patch.object(native, 'tool', side_effect=tool):
            native.prepare(root, 'aarch64-darwin')
        changed = [args[-1].name for name, args in events if name == 'install_name_tool']
        self.assertEqual(changed, ['charon', 'charon-driver', 'charon-driver', 'charon-driver'])
        self.assertIn('@loader_path/../../rust/lib/' + DRIVER, dependencies[paths['charon-driver']])
        signed = [args[-1].name for name, args in events if name == 'codesign' and '--force' in args]
        self.assertEqual(signed, ['charon', 'charon-driver'])
        verified = {args[-1] for name, args in events if name == 'codesign' and '--verify' in args}
        self.assertEqual(verified, set(paths.values()))
        self.assertEqual(before, {name: path.read_bytes() for name, path in paths.items()})

    def test_missing_gmp_and_assembled_sdk_fail_before_any_relocation(self):
        root, paths, _, _, tool = self.fixture()
        paths['gmp'].unlink()
        with patch.object(native, 'tool', side_effect=tool) as static:
            with self.assertRaises(FileNotFoundError):
                native.prepare(root, 'aarch64-darwin')
            static.assert_not_called()
        (root / 'lean-sdk').mkdir()
        with patch.object(native, 'tool') as static:
            with self.assertRaisesRegex(ValueError, 'precede SDK'):
                native.prepare(root, 'aarch64-darwin')
            static.assert_not_called()

    def test_symbol_using_substitution_requires_new_abi_review(self):
        for dependency, symbol in [(ICONV, 'libiconv'), (ZLIB, 'libz')]:
            with self.assertRaisesRegex(ValueError, 'ABI review'):
                native.changes('charon-driver', [dependency], '_example (from ' + symbol + ')')
        unknown = '/nix/store/unknown-libiconv-999/lib/libiconv.2.dylib'
        self.assertEqual(native.changes('charon-driver', [unknown], ''), {})

    def test_unknown_native_dependency_is_rejected_instead_of_host_search(self):
        root, paths, dependencies, _, tool = self.fixture()
        dependencies[paths['gmp']] = ['/nix/store/foreign/lib/libfuture.dylib']
        with patch.object(native, 'tool', side_effect=tool):
            with self.assertRaisesRegex(ValueError, 'unrecognized native reference'):
                native.prepare(root, 'aarch64-darwin')

    def test_provider_resolution_rejects_escapes_missing_and_ambiguous_files(self):
        root, paths, _, _, _ = self.fixture()
        driver = paths['charon-driver']
        rpaths = ['@loader_path/../../rust/lib', '@loader_path/libs']
        self.assertEqual(native.provider('@rpath/' + DRIVER, driver, root, rpaths), paths['driver'])
        with self.assertRaisesRegex(ValueError, 'missing or ambiguous'):
            native.provider('@rpath/' + DRIVER, driver, root, [])
        with self.assertRaises(ValueError):
            native.provider('@rpath/missing.dylib', driver, root, [])
        duplicate = paths['gmp'].parent / DRIVER
        duplicate.write_bytes(b'another provider')
        with self.assertRaisesRegex(ValueError, 'ambiguous'):
            native.provider('@rpath/' + DRIVER, driver, root, rpaths)
        with self.assertRaisesRegex(ValueError, 'unrecognized'):
            native.provider('/opt/homebrew/lib/libgmp.10.dylib', driver, root, [])
        outside = root / 'foreign.dylib'
        outside.write_bytes(b'not an admitted provider')
        with self.assertRaisesRegex(ValueError, 'escapes owned'):
            native.provider('@loader_path/../../foreign.dylib', driver, root, [])
        (root / 'foreign').mkdir()
        with self.assertRaisesRegex(ValueError, 'search directory escapes'):
            native.provider('@rpath/' + DRIVER, driver, root, ['@loader_path/../../foreign'])
        self.assertFalse(native.system('/usr/lib/../../foreign.dylib'))

    def test_missing_or_escaping_driver_is_rejected_before_relocation(self):
        for escape in [False, True]:
            root, paths, _, events, tool = self.fixture()
            paths['driver'].unlink()
            if escape:
                outside = root / 'foreign-driver.dylib'
                outside.write_bytes(b'foreign')
                paths['driver'].symlink_to(outside)
            with patch.object(native, 'tool', side_effect=tool):
                with self.assertRaises((ValueError, FileNotFoundError)):
                    native.prepare(root, 'aarch64-darwin')
            self.assertFalse(any(name == 'install_name_tool' for name, _ in events))

    def test_wrong_architecture_is_rejected_before_relocation(self):
        root, _, _, events, inspect = self.fixture()
        def tool(name, *args):
            return 'x86_64' if name == 'lipo' else inspect(name, *args)
        with patch.object(native, 'tool', side_effect=tool):
            with self.assertRaisesRegex(ValueError, 'architecture'):
                native.prepare(root, 'aarch64-darwin')
        self.assertFalse(any(name == 'install_name_tool' for name, _ in events))

    def test_ineffective_relocation_and_signing_failure_cannot_pass(self):
        for failure in ['relocation', 'signing']:
            root, _, _, _, inspect = self.fixture()
            def tool(name, *args):
                if failure == 'relocation' and name == 'install_name_tool':
                    return ''
                if failure == 'signing' and name == 'codesign' and '--force' in args:
                    raise RuntimeError('signing failed')
                return inspect(name, *args)
            with patch.object(native, 'tool', side_effect=tool):
                with self.assertRaises((ValueError, RuntimeError)):
                    native.prepare(root, 'aarch64-darwin')

    def test_unused_rpath_is_checked_without_an_rpath_dependency(self):
        for rpath in ['relative/foreign', '@future/path', '/opt/homebrew/lib']:
            root, paths, _, _, inspect = self.fixture()
            def tool(name, *args):
                output = inspect(name, *args)
                if name == 'otool' and args[-1] == paths['aeneas']:
                    output += 'cmd LC_RPATH\npath ' + rpath + ' (offset 12)\n'
                return output
            with patch.object(native, 'tool', side_effect=tool):
                with self.assertRaises((ValueError, FileNotFoundError)):
                    native.prepare(root, 'aarch64-darwin')

    def test_macho_inspector_distinguishes_install_id_loader_and_rpath(self):
        result = native.loads('cmd LC_ID_DYLIB\nname @rpath/self.dylib (offset 24)\n'
            'cmd LC_LOAD_DYLIB\nname @rpath/provider.dylib (offset 24)\n'
            'cmd LC_RPATH\npath @loader_path/../lib (offset 12)\n'
            'cmd LC_LOAD_DYLINKER\nname /usr/lib/dyld (offset 12)\n')
        self.assertEqual(result, {'identity': '@rpath/self.dylib', 'needed': ['@rpath/provider.dylib'],
            'rpaths': ['@loader_path/../lib'], 'interpreter': '/usr/lib/dyld'})


if __name__ == '__main__':
    unittest.main()
