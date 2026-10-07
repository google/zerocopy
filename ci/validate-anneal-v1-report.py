#!/usr/bin/env python3
"""Summarize the native V1 run and propose exact harness-generated snapshot diffs."""
import difflib
import json
from pathlib import Path
import re
import sys
import tomllib

repo, evidence = (Path(p).resolve() for p in sys.argv[1:3])
fixtures = repo / 'anneal/v1/tests/fixtures'
configs = {}
configured_snapshots = set()
for path in fixtures.rglob('anneal.toml'):
    config = tomllib.loads(path.read_text()).get('test', {})
    configs[path.parent.name] = config
    for phase in [config, *config.get('phases', [])]:
        for key in ['stderr_file', 'stdout_file']:
            if key in phase:
                configured_snapshots.add(path.parent.relative_to(fixtures) / phase[key])

commands = []
for line in (evidence / 'fixtures-profile.jsonl').read_text().splitlines():
    event = json.loads(line)
    if event.get('event') != 'command':
        continue
    config = configs[event['test']]
    phase = next((p for p in config.get('phases', []) if p['name'] == event.get('phase')), {})
    expected = phase.get('expected_status', config.get('expected_status', 'success'))
    status = event['status_code']
    matches = None if expected == 'known_flaky' else status == 0 if expected == 'success' else status is not None and status != 0
    commands.append({
        'fixture': event['test'], 'phase': event.get('phase'),
        'expected_status': expected, 'actual_status': status,
        'matches_expected_status': matches,
        'argv': event['argv'], 'cwd': event.get('cwd'),
        'duration_ms': event['duration_ms'],
        'stdout_bytes': event.get('stdout_bytes'), 'stderr_bytes': event.get('stderr_bytes'),
    })

statuses = {}
for name in ['units', 'fixtures', 'ordinary-success', 'ordinary-false-post']:
    path = evidence / (name + '.status.json')
    statuses[name] = json.loads(path.read_text()) if path.exists() else None
fixture_exit = (statuses['fixtures'] or {}).get('command_exit')
unit_log = (evidence / 'units.log').read_text(errors='replace')
full_log = (evidence / 'fixtures.log').read_text(errors='replace')
false_log_path = evidence / 'ordinary-false-post.log'
false_log = false_log_path.read_text(errors='replace') if false_log_path.exists() else ''
false_log = re.sub(r'\x1b\[[0-?]*[ -/]*[@-~]', '', false_log)

sidecars = evidence / 'fixture-outputs/snapshots'
patch = []
changed = []
observed = []
for actual in sorted(sidecars.rglob('*')):
    if not actual.is_file():
        continue
    relative = actual.relative_to(sidecars)
    if relative not in configured_snapshots:
        raise RuntimeError(f'unconfigured snapshot sidecar: {relative}')
    expected = fixtures / relative
    before = expected.read_text().replace('\r\n', '\n')
    after = actual.read_text()
    observed.append(str(relative))
    if before != after:
        label = str(expected.relative_to(repo))
        patch.extend(difflib.unified_diff(before.splitlines(keepends=True), after.splitlines(keepends=True), fromfile='a/' + label, tofile='b/' + label))
        changed.append(str(relative))
(evidence / 'snapshot-proposal.patch').write_text(''.join(patch))

checks = {
    'fixture_count_98': len(configs) == 98,
    'all_recorded_logs_written': all(s is not None and s.get('log_exit') == 0 for s in statuses.values()),
    'unit_exit_zero': (statuses['units'] or {}).get('command_exit') == 0,
    'unit_233_passed': bool(re.search(r'test result: ok\. 233 passed; 0 failed;', unit_log)),
    'all_executed_expected_statuses_match': all(c['matches_expected_status'] is not False for c in commands),
    'ordinary_success_accepted': (statuses['ordinary-success'] or {}).get('command_exit') == 0,
    'false_post_rejected_for_unsolved_false': (statuses['ordinary-false-post'] or {}).get('command_exit') not in (None, 0) and all(s in false_log for s in ['unsolved goals', 'False', 'Lean verification failed']),
    'complete_phase_coverage_if_suite_green': fixture_exit != 0 or len(commands) == 103,
}
report = {
    'fixture_count': len(configs), 'expected_complete_commands': 103,
    'executed_commands': len(commands), 'complete_phase_coverage': len(commands) == 103,
    'suite_exit': fixture_exit, 'statuses': statuses,
    'runner_summary': re.findall(r'test result: .*', full_log),
    'failed_fixtures': re.findall(r'^    run_integration_test::(.+)$', full_log, re.M),
    'checks': checks, 'status_mismatches': [c for c in commands if c['matches_expected_status'] is False],
    'changed_snapshot_sidecars': changed,
    'unobserved_configured_snapshots': sorted(str(p) for p in configured_snapshots if str(p) not in observed),
    'commands': commands,
    'snapshot_policy': 'Proposal comes only from the unchanged harness sanitizer. No BLESS, fixture mutation, status bypass, or cross-host target normalization.',
}
(evidence / 'status-report.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k not in ['commands', 'statuses']}, indent=2))
if not all(checks.values()):
    raise SystemExit(1)
