"""Scratch-only stock Lake native-plugin experiment; run only in guarded sequence.

Preparation creates consumer-owned workspaces. It never edits the Aeneas bundle,
Lean sysroot, or repository. Execution is opt-in via --run-smoke / --run-v1.
"""

import argparse
import json
from pathlib import Path

from probes import BACKEND, ROOT, SLUG
from real_sdk_lake import SDK, invoke, workspace


PLUGIN = BACKEND / '.lake/build/lib/libaeneas_AeneasMeta.dylib'
SMOKE = '''import AeneasMeta.Saturate.Tactic

example : True := by
  aeneas_saturate <;> trivial
'''


def plugin_config(package_name: str, libraries: str) -> str:
    # Lake v4.30.0-rc2: PackageConfig.plugins is TargetArray Dynlib. A target
    # key is used here because the package declaration precedes target syntax.
    # inputFile ... false traces the immutable binary's bytes as a dependency.
    return f'''import Lake
open Lake DSL

package {package_name} where
  plugins := #[Target.mk (.mk (.packageTarget .anonymous `aeneasMetaPlugin))]

target aeneasMetaPlugin : Dynlib := do
  let artifact : System.FilePath := "{PLUGIN}"
  return (← inputFile artifact false).map fun path =>
    {{ path := path, name := "aeneas_AeneasMeta", plugin := true }}

{libraries}'''


def tiny_smoke(name: str = 'native-lake-smoke') -> Path:
    w = ROOT / 'work' / name
    w.mkdir(parents=True, exist_ok=True)
    (w / 'lean-toolchain').write_text((BACKEND / 'lean-toolchain').read_text())
    (w / 'Smoke.lean').write_text(SMOKE)
    (w / 'lakefile.lean').write_text(plugin_config(
        'native_lake_smoke',
        '@[default_target] lean_lib Smoke where\n  roots := #[`Smoke]\n',
    ))
    return w


def v1_workspace(name: str = 'native-lake-v1') -> Path:
    w = workspace(name)
    (w / 'lakefile.lean').write_text(plugin_config(
        'anneal_verification',
        f'''@[default_target] lean_lib Generated where
  srcDir := "generated"
  roots := #[`Generated, `{SLUG}.Funs, `{SLUG}.Types]
@[default_target] lean_lib Anneal where
  srcDir := "anneal"
  roots := #[`Config, `SdkIdentity, `Anneal]
''',
    ))
    return w


def report_config(w: Path) -> None:
    print('NATIVE_LAKE_CONFIG', json.dumps({
        'workspace': str(w), 'plugin': str(PLUGIN),
        'plugin_exists': PLUGIN.is_file(), 'sdk': str(SDK),
        'lakefile': str(w / 'lakefile.lean'),
    }), flush=True)


def run_smoke(w: Path) -> None:
    # Each command is guarded and recorded by real_sdk_lake.invoke.
    c = invoke('native-lake-smoke-target', ['lake', '--keep-toolchain', '--no-cache', 'build', 'aeneasMetaPlugin'], w)
    if c['exit'] != 0:
        return
    c = invoke('native-lake-smoke-build', ['lake', '--keep-toolchain', '--no-cache', '--verbose', 'build', '+Smoke:olean'], w)
    if c['exit'] != 0:
        return
    invoke('native-lake-smoke-setup', ['lake', '--keep-toolchain', '--no-cache', 'setup-file', 'Smoke.lean'], w)
    (w / 'SmokeFalse.lean').write_text('import AeneasMeta.Saturate.Tactic\nexample : False := by\n  aeneas_saturate\n')
    invoke('native-lake-smoke-false', ['lake', '--keep-toolchain', '--no-cache', 'lean', 'SmokeFalse.lean'], w)


def run_v1(w: Path) -> None:
    from real_sdk_lake import build
    if not build(w, 'native-lake-v1-build'):
        return
    spec = (w / f'generated/{SLUG}/Specs.lean').read_text()
    positive = spec + '\n#print axioms expand_output.foo.spec\n'
    (w / 'Audit.lean').write_text(positive)
    invoke('native-lake-v1-audit', ['lake', '--keep-toolchain', '--no-cache', 'lean', 'Audit.lean'], w)
    invoke('native-lake-v1-setup', ['lake', '--keep-toolchain', '--no-cache', 'setup-file', 'Audit.lean'], w)
    (w / 'FalseProof.lean').write_text(positive.replace(
        'structure Post  : Prop where',
        'structure Post  : Prop where\n    contradiction : False',
    ))
    invoke('native-lake-v1-false', ['lake', '--keep-toolchain', '--no-cache', 'lean', 'FalseProof.lean'], w)
    (w / 'SorryProof.lean').write_text(positive.replace('exact\n      ⟨⟩', 'sorry'))
    invoke('native-lake-v1-sorry', ['lake', '--keep-toolchain', '--no-cache', 'lean', 'SorryProof.lean'], w)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--prepare-smoke', action='store_true')
    ap.add_argument('--prepare-v1', action='store_true')
    ap.add_argument('--run-smoke', action='store_true')
    ap.add_argument('--run-v1', action='store_true')
    ns = ap.parse_args()
    if ns.prepare_smoke or ns.run_smoke:
        w = tiny_smoke()
        report_config(w)
        if ns.run_smoke:
            run_smoke(w)
    if ns.prepare_v1 or ns.run_v1:
        w = v1_workspace()
        report_config(w)
        if ns.run_v1:
            run_v1(w)
