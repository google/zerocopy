#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.


# Exercise native HIR discovery independently of extraction reachability. Fixtures
# live in a private target directory and never alter the production source census.
set -euo pipefail
[[ $# == 0 ]] || { echo "Usage: $0" >&2; exit 1; }
: "${AENEAS_TOOLCHAIN_DIR:?Set AENEAS_TOOLCHAIN_DIR to the pinned patched runtime}"
cd "$(dirname "$0")/../../.."
repo=$PWD
source verification/aeneas/toolchain.sh
tools_dir=$AENEAS_TOOLCHAIN_DIR
export CARGO_NET_OFFLINE=true
mkdir -p "$repo/target/aeneas"
work=$(mktemp -d "$repo/target/aeneas/annotation-origins.XXXXXX")
trap 'status=$?; if [[ $status == 0 ]]; then rm -rf "$work"; else echo "Native origin control artifacts retained: $work" >&2; fi' EXIT
cat > "$work/origins.rs" <<'RUST'
#![allow(unused)]
unsafe trait Law {}
struct Ordinary;
/// ```aeneas
/// invariant_proof
/// ```
unsafe impl Law for Ordinary {}
macro_rules! forward { ($(#[$doc:meta])* $ty:ty) => { $(#[$doc])* unsafe impl Law for $ty {} }; }
struct Forwarded;
forward! {
    #[doc = " ```aeneas\n invariant_proof\n ```"]
    Forwarded
}
macro_rules! duplicate { ($(#[$doc:meta])* $a:ty, $b:ty) => { $(#[$doc])* unsafe impl Law for $a {} $(#[$doc])* unsafe impl Law for $b {} }; }
struct First; struct Second;
duplicate! {
    /// ```aeneas
    /// invariant_proof
    /// ```
    First, Second
}
struct Field {
    /// ```aeneas
    /// spec
    /// ```
    value: u8,
}
/// function doc
fn included() {}
fn excluded() {
    /// ```aeneas
    /// spec
    /// ```
    let local = 1;
}

/// public const function doc
pub(crate) const fn with_modifiers() -> u8 { 0 }
/// public unsafe trait doc
pub unsafe trait PublicTrait {}
/// ```aeneas
/// model tuple struct
/// ```
struct TupleModel(u8);
/// ```aeneas
/// model unit struct
/// ```
struct UnitModel;
struct BadTupleField(
    /// ```aeneas
    /// model forbidden tuple field
    /// ```
    u8,
);
enum BadVariant {
    /// ```aeneas
    /// model forbidden variant
    /// ```
    Variant(u8),
}
RUST
python3 -B - "$tools_dir/charon" "$work" <<'PYTEST'
import json
import os
from pathlib import Path
import subprocess
import sys

charon = Path(sys.argv[1])
work = Path(sys.argv[2])
fixture = work / 'origins.rs'
data = fixture.read_bytes()
steps = []


def run(label, selector, source=fixture, diagnostic=None):
    env = os.environ.copy()
    # macOS protected interpreters may drop inherited DYLD variables. Restore
    # the pinned runtime's library location inside the subprocess environment.
    libraries = str(charon.parent / 'rust/lib')
    env['DYLD_LIBRARY_PATH'] = libraries + ':' + str(charon.parent / 'libs')
    env['LD_LIBRARY_PATH'] = libraries + ':' + str(charon.parent / 'libs')
    env['CHARON_ANNOTATION_ORIGINS'] = str(work / (label + '.origins.json'))
    env['CHARON_ADMISSION_SNAPSHOT'] = str(work / (label + '.before.ullbc'))
    command = [
        str(charon), 'rustc', '--preset=aeneas', '--sysroot', 'default',
        '--start-from', selector, '--mir', 'promoted', '--no-dedup-serialized-ast',
        '--dest-file', str(work / (label + '.llbc')), '--abort-on-error',
        '--error-on-warnings', '--', '--crate-name', 'native_origin',
        '--crate-type', 'lib', source.name,
    ]
    result = subprocess.run(command, cwd=work, env=env, text=True, capture_output=True)
    log = result.stdout + result.stderr
    (work / (label + '.log')).write_text(log)
    steps.append({'case': label, 'selector': selector, 'exit': result.returncode,
                  'diagnostic': diagnostic, 'command': command})
    (work / 'commands.json').write_text(json.dumps(steps, indent=2) + '\n')
    if diagnostic is not None:
        assert result.returncode != 0 and diagnostic in log, (label, log)
        return None
    assert result.returncode == 0, (label, log)
    return json.loads((work / (label + '.origins.json')).read_text())


def origin(node):
    doc = node['docs'][0]
    return f"@doc-origin:{doc['file']}:{doc['begin']}:{doc['end']}"


# Every positive extraction must pass before any expected failure is attempted.
# Operational failures therefore cannot count as successful negative controls.
baseline = run('selected-function-census', 'native_origin::included')
assert baseline['version'] == 1
nodes = baseline['nodes']
impls = [node for node in nodes if node['node_kind'] == 'trait-impl']
assert len(impls) == 4 and all(node['positive'] for node in impls), impls
assert all(node['trait_impl_id'] is None for node in impls), impls
assert next(source['text'] for source in baseline['sources']
            if source['file'] == fixture.name) == data.decode()

# rustc aliases tuple/unit docs onto a synthetic ctor. Only that exact nominal
# compiler alias may be folded; independent field/variant/statement docs survive.
for name in ['TupleModel', 'UnitModel']:
    owners = [node for node in nodes if node['owner'].endswith(name)]
    assert len(owners) == 1 and owners[0]['node_kind'] == 'type', owners
for text in ['forbidden tuple field', 'forbidden variant']:
    owners = [node for node in nodes if any(text in doc['text'] for doc in node['docs'])]
    assert owners and all(node['node_kind'] == 'unsupported' for node in owners), owners
for marker in [b'    value: u8,', b'    let local = 1;']:
    owners = [node for node in nodes if node['span']['begin'] == data.index(marker.lstrip())]
    assert owners and all(node['node_kind'] == 'unsupported' for node in owners), owners
    if marker == b'    let local = 1;':
        assert len(owners) == 2, owners  # Both Stmt and LetStmt aliases are censused.
for name, start in [('with_modifiers', b'pub(crate) const fn'),
                    ('PublicTrait', b'pub unsafe trait')]:
    node = next(node for node in nodes if node['owner'].endswith(name))
    assert node['span']['begin'] == data.index(start), node

raw = next(node for node in impls
           if any('invariant_proof' in doc['text'] and '\n' in doc['text']
                  for doc in node['docs']))
selected = run('macro-unique', origin(raw))
selected_impl = next(node for node in selected['nodes'] if node['owner'] == raw['owner'])
impl_id = selected_impl['trait_impl_id']
assert type(impl_id) is int
before = json.loads((work / 'macro-unique.before.ullbc').read_text())
final = json.loads((work / 'macro-unique.llbc').read_text())
assert selected_impl['trait_impl'] == before['translated']['trait_impls'][impl_id]
assert final['translated']['trait_impls'][impl_id] is not None
ordinary = next(node for node in impls
                if node['span']['begin'] == data.index(b'unsafe impl Law for Ordinary'))
run('direct-doc-origin', origin(ordinary))
span = ordinary['span']
run('span-preserved', f"@span:{span['file']}:{span['begin']}:{span['end']}")

# Value spans and sugared comment spans use physical byte positions even though
# rustc's captured source text has normalized CRLF and removed the leading BOM.
bom = work / 'bom-crlf.rs'
bom_data = ('\ufeff#![allow(unused)]\r\nunsafe trait Law {}\r\nstruct Bytes;\r\n'
            '/// ```aeneas\r\n/// invariant_proof\r\n/// ```\r\n'
            '#[doc = r#" literal é"#]\r\nunsafe impl Law for Bytes {}\r\n'
            'fn included() {}\r\n').encode()
bom.write_bytes(bom_data)
normalized = run('bom-crlf', 'native_origin::included', source=bom)
bom_impl = next(node for node in normalized['nodes'] if node['node_kind'] == 'trait-impl')
assert bom_impl['docs'][0]['begin'] == bom_data.index(b'/// ```aeneas')
literal = bom_impl['docs'][-1]
spelling = 'r#" literal é"#'.encode()
assert literal['begin'] == bom_data.index(spelling)
assert literal['end'] == literal['begin'] + len(spelling)
assert literal['text'] == ' literal é'
assert next(source['text'] for source in normalized['sources']
            if source['file'] == bom.name) == bom_data.decode('utf-8-sig').replace('\r\n', '\n')

# Repeated forwarding remains two distinct native owners, so selecting its
# shared fragment must fail with a cardinality diagnostic. A missing fragment
# must fail semantically too; compiler startup errors do not satisfy either test.
counts = {}
for node in impls:
    for doc in node['docs']:
        counts.setdefault((doc['file'], doc['begin'], doc['end']), []).append(node)
duplicated = next(owners for owners in counts.values() if len(owners) == 2)
assert len({node['owner'] for node in duplicated}) == 2
run('duplicate-rejected', origin(duplicated[0]),
    diagnostic='matched 2 positive local trait impls; expected exactly one')
run('missing-rejected', f'@doc-origin:{fixture.name}:1:2',
    diagnostic='matched 0 positive local trait impls; expected exactly one')
print('Native annotation-origin controls passed (5 positive extractions, 2 semantic failures)')
PYTEST
