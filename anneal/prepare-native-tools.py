#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Relocate and statically check Darwin translation tools in new archive staging.

Never invokes translated tools, compilers, or the Lean SDK publisher. This is
separate from the Lean-consumed closure and its identity. System libraries are
an explicit Darwin platform assumption; this is not dynamic ABI acceptance.
"""
import argparse
from pathlib import Path
import re
import subprocess


def tool(name, *args):
    return subprocess.run(['/usr/bin/' + name, *map(str, args)], check=True,
                          capture_output=True, text=True, timeout=60,
                          env={'PATH': '/usr/bin:/bin:/usr/sbin:/sbin', 'LC_ALL': 'C'}).stdout


def loads(text):
    result = {'needed': [], 'rpaths': [], 'identity': None, 'interpreter': None}
    command = None
    for line in text.splitlines():
        line = line.strip()
        if line.startswith('cmd '):
            command = line.split()[1]
        elif line.startswith('name ') and command:
            name = line[5:].rsplit(' (offset ', 1)[0]
            if command == 'LC_ID_DYLIB':
                result['identity'] = name
            elif command == 'LC_LOAD_DYLINKER':
                result['interpreter'] = name
            elif command in {'LC_LOAD_DYLIB', 'LC_LOAD_WEAK_DYLIB', 'LC_REEXPORT_DYLIB', 'LC_LOAD_UPWARD_DYLIB', 'LC_LAZY_LOAD_DYLIB'}:
                result['needed'].append(name)
        elif line.startswith('path ') and command == 'LC_RPATH':
            result['rpaths'].append(line[5:].rsplit(' (offset ', 1)[0])
    return result


def changes(name, dependencies, symbols):
    result = {}
    for dependency in dependencies:
        replacement = None
        if name in {'charon', 'charon-driver'}:
            if re.fullmatch(r'/nix/store/[^/]+-libiconv-109/lib/libiconv\.2\.dylib', dependency):
                replacement = '/usr/lib/libiconv.2.dylib'
            elif name == 'charon-driver' and re.fullmatch(r'/nix/store/[^/]+-zlib-1\.3\.1/lib/libz\.dylib', dependency):
                replacement = '/usr/lib/libz.1.dylib'
            elif name == 'charon-driver' and re.fullmatch(r'@rpath/librustc_driver-[0-9a-f]+\.dylib', dependency):
                # System shell shims on macOS strip DYLD_LIBRARY_PATH. The
                # archive already fixes this provider beside the tools.
                result[dependency] = '@loader_path/../../rust/lib/' + dependency[len('@rpath/'):]
                continue
        if replacement:
            family = 'libiconv' if 'iconv' in replacement else 'libz'
            if re.search(r'\(from ' + family + r'[^)]*\)', symbols):
                raise ValueError('system substitution needs a new ABI review: ' + dependency)
            result[dependency] = replacement
    return result


def system(reference):
    return '..' not in Path(reference).parts and reference.startswith(('/usr/lib/', '/System/Library/Frameworks/'))


def owned(path, root):
    path = path.resolve(strict=True)
    if not path.is_file() or not any(path.is_relative_to(root / family) for family in ('aeneas/bin', 'rust/lib')):
        raise ValueError('native provider escapes owned archive payload: ' + str(path))
    return path


def provider(reference, image, root, rpaths):
    if system(reference):
        return None
    def expand(value):
        value = value.replace('@loader_path', str(image.parent)).replace('@executable_path', str(root / 'aeneas/bin'))
        if '@' in value or '$' in value or not Path(value).is_absolute():
            raise ValueError('unsupported native path: ' + value)
        return Path(value)
    if reference.startswith(('@loader_path/', '@executable_path/')):
        return owned(expand(reference), root)
    if reference.startswith('@rpath/'):
        name = reference[len('@rpath/'):]
        if '/' in name:
            raise ValueError('unsupported nested rpath provider: ' + reference)
        # Physical presence alone does not make a dyld search path. In
        # particular a system shell can discard DYLD_LIBRARY_PATH.
        directories = [expand(path).resolve(strict=True) for path in rpaths]
        for directory in directories:
            if not directory.is_dir() or not any(directory.is_relative_to(root / family) for family in ('aeneas/bin', 'rust/lib')):
                raise ValueError('loader search directory escapes owned archive payload: ' + str(directory))
        candidates = {owned(directory / name, root) for directory in directories if (directory / name).exists()}
        if len(candidates) != 1:
            raise ValueError('missing or ambiguous native provider: ' + reference)
        return candidates.pop()
    raise ValueError('non-system or unrecognized native reference: ' + reference)


def prepare(root, platform):
    root = root.resolve(strict=True)
    if (root / 'lean-sdk').exists():
        raise ValueError('translation relocation must precede SDK assembly')
    architecture = {'aarch64-darwin': 'arm64', 'x86_64-darwin': 'x86_64'}[platform]
    pending = [owned(root / 'aeneas/bin' / name, root) for name in ('aeneas', 'charon', 'charon-driver')]
    owned(root / 'aeneas/bin/libs/libgmp.10.dylib', root)
    plans = []
    for image in pending:
        if architecture not in tool('lipo', '-archs', image).split():
            raise ValueError('native provider lacks selected architecture: ' + str(image))
        information = loads(tool('otool', '-l', image))
        symbols = tool('nm', '-m', '-u', image) if image.name in {'charon', 'charon-driver'} else ''
        replacements = changes(image.name, information['needed'], symbols)
        for new in replacements.values():
            if new.startswith('@loader_path/'):
                provider(new, image, root, [])
        plans.append((image, replacements))
    for image, replacements in plans:
        for old, new in replacements.items():
            tool('install_name_tool', '-change', old, new, image)
        if replacements:
            tool('codesign', '--force', '--sign', '-', '--timestamp=none', image)
    visited = set()
    while pending:
        image = owned(pending.pop(), root)
        if image in visited:
            continue
        visited.add(image)
        if architecture not in tool('lipo', '-archs', image).split():
            raise ValueError('native provider lacks selected architecture: ' + str(image))
        information = loads(tool('otool', '-l', image))
        if information['interpreter'] not in (None, '/usr/lib/dyld'):
            raise ValueError('foreign native interpreter')
        identity = information['identity']
        if identity and identity.startswith('/') and not system(identity):
            raise ValueError('non-system absolute native install ID')
        for path in information['rpaths']:
            if system(path):
                continue
            expanded = path.replace('@loader_path', str(image.parent)).replace('@executable_path', str(root / 'aeneas/bin'))
            if '@' in expanded or '$' in expanded or not Path(expanded).is_absolute():
                raise ValueError('unsupported native rpath: ' + path)
            directory = Path(expanded).resolve(strict=True)
            if not directory.is_dir() or not any(directory.is_relative_to(root / family) for family in ('aeneas/bin', 'rust/lib')):
                raise ValueError('native rpath escapes owned payload: ' + path)
        for reference in information['needed']:
            dependency = provider(reference, image, root, information['rpaths'])
            if dependency:
                pending.append(dependency)
        tool('codesign', '--verify', '--strict', image)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--platform', choices=['aarch64-darwin', 'x86_64-darwin'], required=True)
    args = parser.parse_args()
    prepare(args.root, args.platform)
