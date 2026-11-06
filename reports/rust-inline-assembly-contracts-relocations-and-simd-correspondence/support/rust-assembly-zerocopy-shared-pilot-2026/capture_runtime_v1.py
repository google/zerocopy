#!/usr/bin/env python3
"""Prepared E46 positive runtime capture. DO NOT INVOKE before parent grant.

Only the fixed four original positive images can run, once, in this order.
No compilation, guest feature probe, mutant execution, shell or retry API.
All host writes are create-only and confined to runtime-captures-v1/.
"""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time
import traceback

ROOT = Path(__file__).absolute().parent
POLICY_SHA = "40895bfd66a333bf2aea2fd7e8ca84af278c26d718a251fcc2248781875d2e6f"
FREEZE_SHA = "e4de79c8b18cdb1f8735cef55e89c231eba4087c9da2065b31073fbb5ab50c3f"
PROPOSAL_SHA = "b4855757ea4b0d0b5096c12274432cdf8af1b50cc7d1938e04bcdc2f42aba186"
CID = "c1bf0a443c09a62a7747793d9ce696edfea27dbdc58bbacc652a4d999212c2d5"
TC = "/usr/local/rustup/toolchains/1.89.0-aarch64-unknown-linux-gnu"
CAP = 256 * 1024 * 1024
ENV = {"PATH": "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
       "LC_ALL": "C", "TZ": "UTC"}
FIXED = [
    ("aarch64-O0-positive", ["build/aarch64/O0/pilot"],
     "adb86a7669598af8b9fa65d84bdea9b652fbc95171bff686fa3af85a24d10f20"),
    ("aarch64-O3-positive", ["build/aarch64/O3/pilot"],
     "b8047348558fdbc9fb7335e561dbb93f2983a9158f6604b26cfe8ae3d82f87f8"),
    ("x86_64-O0-positive", ["/usr/bin/qemu-x86_64", "-cpu", "qemu64-v1",
                            "-L", "/usr/x86_64-linux-gnu", "build/x86_64/O0/pilot"],
     "ab6265e1c5333c11e971973b39b4cbc0a1ada16763c8c70515b8d881ce40ed4c"),
    ("x86_64-O3-positive", ["/usr/bin/qemu-x86_64", "-cpu", "qemu64-v1",
                            "-L", "/usr/x86_64-linux-gnu", "build/x86_64/O3/pilot"],
     "64a1efa22c13b1b01e540193225fc50f7dd3911cd387a592165f7fe566c7a144"),
]

# Executed only as the reviewed read-only metadata reader, not as a guest probe.
SNAPSHOT = r'''
from pathlib import Path
import hashlib,json,os,stat,sys
request=json.loads(sys.argv[1]);root=Path('/e46');tc=Path(request['toolchain'])
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while True:
   chunk=f.read(1024*1024)
   if not chunk:break
   h.update(chunk)
 return h.hexdigest()
def item(p,label):
 s=p.stat()
 return {'path':label,'bytes':s.st_size,'sha256':digest(p),
         'mode':oct(stat.S_IMODE(s.st_mode)),'resolved':str(p.resolve())}
out={'inputs':[],'target_libraries':[],'tools':[],'outputs':[],
     'runtime_libraries':[],'metadata_tools':[],'errors':[]}
for kind,base in [('inputs',root),('target_libraries',tc),('tools',Path('/')),
                  ('outputs',root)]:
 for e in request['baseline'][kind]:
  p=base/e['path']
  if not p.is_file():out['errors'].append('missing file '+str(p));continue
  if kind in ['inputs','target_libraries','outputs'] and p.is_symlink():
   out['errors'].append('unexpected symlink '+str(p));continue
  got=item(p,e['path']);out[kind].append(got)
  if got!=e:out['errors'].append('frozen identity '+str(p))
actual_outputs=[str(p.relative_to(root)) for p in sorted((root/'build').rglob('*'))
                if p.is_file() or p.is_symlink()]
if actual_outputs!=[e['path'] for e in request['baseline']['outputs']]:
 out['errors'].append('build output file set changed')
for e in request['runtime_libraries']:
 p=Path(e['path'])
 got={'path':e['path'],'exists':p.is_file(),'symlink':p.is_symlink()}
 if p.is_file():
  got.update({'resolved':str(p.resolve()),'bytes':p.stat().st_size,'sha256':digest(p)})
  with p.open('rb') as f:got['ELF_identity']=f.read(18).hex()
 out['runtime_libraries'].append(got)
 if got!=e:out['errors'].append('runtime library identity '+str(p))
for e in request['metadata_tools']:
 p=Path(e['path'])
 if not p.is_file():out['errors'].append('missing metadata tool '+str(p));continue
 got=item(p,e['path']);resolved=p.resolve(strict=True)
 link=os.readlink(p) if p.is_symlink() else None
 got.update({'path_is_symlink':p.is_symlink(),
             'path_lstat_mode':oct(stat.S_IMODE(p.lstat().st_mode)),
             'link_target':link,
             'link_literal_sha256':hashlib.sha256(os.fsencode(link)).hexdigest() if link is not None else None,
             'resolved_target':{'path':str(resolved),'bytes':resolved.stat().st_size,
                                'sha256':digest(resolved),
                                'mode':oct(stat.S_IMODE(resolved.stat().st_mode))}})
 out['metadata_tools'].append(got)
 if got!=e:out['errors'].append('metadata tool identity '+str(p))
out['metadata_python_executable']=sys.executable
if out['metadata_python_executable']!=request['metadata_python_executable']:
 out['errors'].append('metadata interpreter executable path changed')
out['native_machine']=os.uname().machine
if out['native_machine']!='aarch64':out['errors'].append('native process architecture changed')
out['output_bytes']=sum(e['bytes'] for e in out['outputs'])
if out['output_bytes']>request['cap']:out['errors'].append('generated output cap exceeded')
out['cgroup_readings']={}
for name in ['cpu.max','memory.max','memory.current','memory.events','pids.max','pids.current']:
 p=Path('/sys/fs/cgroup')/name
 out['cgroup_readings'][name]=p.read_text() if p.is_file() else None
print(json.dumps(out,indent=2))
sys.exit(2 if out['errors'] else 0)
'''


class CaptureStop(Exception):
    pass


def need(condition, reason):
    if not condition:
        raise CaptureStop(reason)


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def create_json(path, value):
    with path.open("x") as stream:
        json.dump(value, stream, indent=2)
        stream.write("\n")


def create_bytes(path, value):
    with path.open("xb") as stream:
        stream.write(value)


def check_frozen_host(policy, reviewed_preparation_sha):
    need(ROOT.resolve() == ROOT and not ROOT.is_symlink(), "Owned physical root changed")
    preparation = ROOT / "RUNTIME-CAPTURE-PREPARATION.json"
    need(digest(preparation) == reviewed_preparation_sha, "Reviewed capture preparation changed")
    for entry in json.loads(preparation.read_text())["files"]:
        path = ROOT / entry["path"]
        need(path.is_file() and not path.is_symlink(), "Missing/nonregular capture input " + entry["path"])
        need(path.stat().st_size == entry["bytes"] and digest(path) == entry["sha256"],
             "Capture input changed " + entry["path"])
    frozen = ROOT / "COMPILE-STATIC-FREEZE.json"
    need(digest(frozen) == FREEZE_SHA, "Static freeze changed")
    for entry in json.loads(frozen.read_text())["files"]:
        path = ROOT / entry["path"]
        need(path.is_file() and not path.is_symlink(), "Missing/nonregular frozen file " + entry["path"])
        need(path.stat().st_size == entry["bytes"] and digest(path) == entry["sha256"],
             "Frozen file identity changed " + entry["path"])
    need(digest(ROOT / "runtime-capture-policy.json") == POLICY_SHA, "Capture policy changed")
    need(digest(ROOT / "compile-static/runtime-proposal.json") == PROPOSAL_SHA,
         "Reviewed runtime proposal changed")
    need(policy["static_freeze_sha256"] == FREEZE_SHA, "Policy freeze mismatch")
    observed = []
    docker = shutil.which("docker")
    need(docker is not None, "Docker CLI missing")
    for expected in policy["host_tools"]:
        actual = Path(sys.executable if expected["label"] == "python" else docker)
        need(actual.is_file(), "Host tool missing")
        row = {"label": expected["label"], "path": str(actual),
               "resolved": str(actual.resolve()), "bytes": actual.stat().st_size,
               "sha256": digest(actual)}
        need(row == expected, "Host tool identity changed: " + expected["label"])
        observed.append(row)
    return docker, observed


def capture(directory, name, argv, timeout):
    started = time.monotonic()
    timed_out, spawn_error = False, None
    try:
        result = subprocess.run(argv, stdin=subprocess.DEVNULL, capture_output=True,
                                timeout=timeout, shell=False)
        code, stdout, stderr = result.returncode, result.stdout, result.stderr
    except subprocess.TimeoutExpired as exc:
        code, stdout, stderr = None, exc.stdout or b"", exc.stderr or b""
        timed_out = True
    except OSError as exc:
        code, stdout, stderr = None, b"", b""
        spawn_error = repr(exc)
    create_bytes(directory / (name + ".stdout"), stdout)
    create_bytes(directory / (name + ".stderr"), stderr)
    receipt = {"argv": argv, "exit": code, "host_timeout": timed_out,
               "spawn_error": spawn_error, "elapsed_seconds": time.monotonic() - started,
               "stdout_bytes": len(stdout), "stderr_bytes": len(stderr),
               "stdout_sha256": hashlib.sha256(stdout).hexdigest(),
               "stderr_sha256": hashlib.sha256(stderr).hexdigest()}
    create_json(directory / (name + ".json"), receipt)
    return receipt, stdout, stderr


def metadata_result(directory, name, argv):
    receipt, stdout, stderr = capture(directory, name, argv, 60)
    need(receipt["exit"] == 0 and not receipt["host_timeout"] and
         receipt["spawn_error"] is None and not stderr, "Metadata capture failed: " + name)
    return json.loads(stdout)


def resources(directory, name, docker, policy):
    rows = metadata_result(directory, name, [docker, "inspect", CID])
    need(len(rows) == 1, "Container inspection cardinality changed")
    row = rows[0]
    need(row["Id"] == CID and row["Image"] == policy["container_image"] and
         row["Name"] == policy["container_name"], "Container/image identity changed")
    state = row["State"]
    need(state["Running"] and state["Status"] == "running" and not any(
        state[key] for key in ["Paused", "Restarting", "OOMKilled", "Dead"]),
        "Container not in healthy running state")
    need(state["StartedAt"] == policy["container_started_at"] and
         row["RestartCount"] == policy["container_restart_count"], "Container restarted since preflight")
    need(row["Mounts"] == [], "Container gained a mount")
    for key, value in policy["resource_expectations"].items():
        need(row["HostConfig"][key] == value, "Container resource/config changed: " + key)
    return {"Id": row["Id"], "Image": row["Image"], "Name": row["Name"],
            "Mounts": row["Mounts"], "StartedAt": state["StartedAt"],
            "RestartCount": row["RestartCount"],
            "limits": {key: row["HostConfig"][key] for key in policy["resource_expectations"]}}


def snapshot(directory, name, docker, policy):
    request = {"toolchain": TC, "cap": CAP, "baseline": policy["snapshot_baseline"],
               "runtime_libraries": policy["runtime_library_files"],
               "metadata_tools": policy["metadata_tools"],
               "metadata_python_executable": policy["metadata_reader_actual_executable"]}
    argv = [docker, "exec", "--workdir", "/e46", CID, "/usr/bin/env", "-i"]
    argv += [key + "=" + value for key, value in sorted(ENV.items())]
    argv += ["/usr/bin/python3", "-c", SNAPSHOT, json.dumps(request)]
    row = metadata_result(directory, name, argv)
    need(row["errors"] == [], "Container file identity mismatch: " + name)
    need([len(row[key]) for key in ["inputs", "target_libraries", "tools", "outputs"]]
         == [28, 69, 12, 20], "Snapshot domain cardinality changed")
    need(len(row["runtime_libraries"]) == 7, "Runtime library-path domain changed")
    need(len(row["metadata_tools"]) == 2, "Reader/wrapper tool domain changed")
    return row


def accepts(expected, receipt, stdout, stderr):
    return (receipt["exit"] == expected["expected_exit"] and
            not receipt["host_timeout"] and receipt["spawn_error"] is None and
            stdout == expected["expected_stdout"].encode() and
            stderr == expected["expected_stderr"].encode())


def output_controls(expected, receipt, stdout, stderr):
    changed_status = dict(receipt, exit=1)
    arch = b"aarch64" if b"arch=aarch64" in stdout else b"x86_64"
    candidates = [
        ("wrong-count", receipt, stdout.replace(b"checks=4617", b"checks=4616", 1), stderr),
        ("wrong-architecture", receipt, stdout.replace(b"arch=" + arch, b"arch=other", 1), stderr),
        ("missing-newline", receipt, stdout[:-1], stderr),
        ("trailing-stdout", receipt, stdout + b"data-only mutation\n", stderr),
        ("nonempty-stderr", receipt, stdout, b"data-only mutation\n"),
        ("nonzero-status", changed_status, stdout, stderr),
    ]
    rows = []
    for ident, changed_receipt, changed_stdout, changed_stderr in candidates:
        rejected = not accepts(expected, changed_receipt, changed_stdout, changed_stderr)
        rows.append({"id": ident, "rejected": rejected,
                     "stdout_hex": changed_stdout.hex(), "stderr_hex": changed_stderr.hex(),
                     "candidate_exit": changed_receipt["exit"],
                     "mutated_process_or_image_executed": False})
    need(all(row["rejected"] for row in rows), "Output matcher accepted a data-only mutant")
    return {"role": "Data-only copies derived from the actual positive receipt; no execution",
            "original_stdout_sha256": receipt["stdout_sha256"],
            "original_stderr_sha256": receipt["stderr_sha256"], "controls": rows,
            "limit": "Receipt/status/one-line-output admission only; not injected wrong results, guards or ABI faults."}


def main():
    need(len(sys.argv) == 3 and sys.argv[1] == "--execute-positive-sequence-after-parent-grant" and
         len(sys.argv[2]) == 64 and all(c in "0123456789abcdef" for c in sys.argv[2]),
         "No default action; pass the parent-reviewed preparation hash after a prior parent grant")
    reviewed_preparation_sha = sys.argv[2]
    policy_path = ROOT / "runtime-capture-policy.json"
    need(digest(policy_path) == POLICY_SHA, "Runtime capture policy identity changed")
    policy = json.loads(policy_path.read_text())
    need(policy["proposal"]["base_environment"] == ENV, "Environment policy changed")
    need(policy["proposal"]["container_id"] == CID, "Container policy changed")
    need(len(policy["proposal"]["runs"]) == 4, "Runtime command count changed")
    # These two ordinary reader/wrapper binaries must be pinned before any call.
    need({row["path"] for row in policy.get("metadata_tools", [])} ==
         {"/usr/bin/env", "/usr/bin/python3"}, "Parent reader/wrapper tool pins required")
    for run, (ident, argv, image_sha) in zip(policy["proposal"]["runs"], FIXED):
        need((run["id"], run["argv"], run["image_sha256"]) == (ident, argv, image_sha),
             "Command/image policy differs from the fixed four positives")
        arch = "aarch64" if ident.startswith("aarch64") else "x86_64"
        need(run["cwd"] == "/e46" and run["environment"] == {} and
             run["timeout_seconds"] == 30 and run["expected_exit"] == 0 and
             run["expected_stderr"] == "" and run["expected_stdout"] ==
             "E46_OK arch=" + arch + " checks=4617 native_or_emulated=external_receipt\n",
             "Runtime scope or oracle changed")
    docker, host_tools = check_frozen_host(policy, reviewed_preparation_sha)
    directory = ROOT / "runtime-captures-v1"
    directory.mkdir(exist_ok=False)  # One attempt only, including failed preflights.
    create_json(directory / "ATTEMPT.json", {"helper_sha256": digest(Path(__file__)),
                "policy_sha256": POLICY_SHA, "static_freeze_sha256": FREEZE_SHA,
                "reviewed_preparation_sha256": reviewed_preparation_sha,
                "proposal_sha256": PROPOSAL_SHA, "host_tools": host_tools,
                "scope": "Four fixed unchanged positive images, serial, once; no retry or mutant execution"})
    stage = "before-first-run"
    summaries = []
    try:
        for run in policy["proposal"]["runs"]:
            ident = run["id"]
            stage = ident + "-before"
            _, host_before = check_frozen_host(policy, reviewed_preparation_sha)
            before_resources = resources(directory, ident + "-before-resources", docker, policy)
            before = snapshot(directory, ident + "-before-files", docker, policy)
            argv = [docker, "exec", "--workdir", "/e46", CID, "/usr/bin/env", "-i"]
            argv += [key + "=" + value for key, value in sorted(ENV.items())]
            argv += ["/usr/bin/timeout", "--signal=KILL", "30s"] + run["argv"]
            stage = ident + "-positive-call"
            receipt, stdout, stderr = capture(directory, ident, argv, 45)
            # After-checks are read-only diagnostics even if the subject failed.
            stage = ident + "-after"
            after = snapshot(directory, ident + "-after-files", docker, policy)
            after_resources = resources(directory, ident + "-after-resources", docker, policy)
            _, host_after = check_frozen_host(policy, reviewed_preparation_sha)
            same_keys = ["inputs", "target_libraries", "tools", "outputs", "runtime_libraries", "metadata_tools"]
            identities_ok = all(before[key] == after[key] for key in same_keys)
            identities_ok = identities_ok and host_before == host_after and before_resources == after_resources
            positive_ok = accepts(run, receipt, stdout, stderr)
            summary = {"id": ident, "image_sha256": run["image_sha256"],
                       "execution_kind": run["execution_kind"], "exit": receipt["exit"],
                       "output_status_match": positive_ok, "identities_resources_unchanged": identities_ok,
                       "expected_checks": 4617, "no_mutant_executed": True}
            create_json(directory / (ident + "-summary.json"), summary)
            need(positive_ok and identities_ok, "Positive status/output/identity/resource mismatch: " + ident)
            create_json(directory / (ident + "-data-only-controls.json"),
                        output_controls(run, receipt, stdout, stderr))
            summaries.append(summary)
            print(json.dumps(summary), flush=True)
        create_json(directory / "SEQUENCE.json", {"status": "four-positive-runs-passed",
                    "runs": summaries, "finite_checks_total": 18468,
                    "data_only_output_controls": 24, "mutants_executed": False,
                    "limit": "Finite corpus observation; no Rust/ISA/compiler/ABI/resource/trace theorem or checkbox decision"})
    except BaseException as exc:
        create_json(directory / "STOP.json", {"stage": stage, "exception": repr(exc),
                    "stop_dependent_work": True, "retry_performed": False,
                    "completed_positive_summaries": summaries})
        create_bytes(directory / "STOP-traceback.txt", traceback.format_exc().encode())
        raise


if __name__ == "__main__":
    main()
