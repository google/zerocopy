#!/usr/bin/env python3
"""E46 compile/static capture only. No target image/guest execution API.

Select only immutable proposed compile commands; run serially with clean env
and GNU timeout. Read-only snapshots bind the 28 staged inputs, 69 target
libraries, tools, and all build files before/after. Write host captures only
under this file's owned root. Docker compiler output stays in /e46/build.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import shutil
import sys
import time

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent / "parent"
CID = "c1bf0a443c09a62a7747793d9ce696edfea27dbdc58bbacc652a4d999212c2d5"
DOCKER = shutil.which("docker")
if DOCKER is None:
    raise SystemExit("docker executable not found; no operation started")
TC = "/usr/local/rustup/toolchains/1.89.0-aarch64-unknown-linux-gnu"
CAP = 256 * 1024 * 1024

SNAPSHOT = r'''
from pathlib import Path
import hashlib,json,stat,sys
request=json.loads(sys.argv[1]);root=Path('/e46');tc=Path(request['toolchain'])
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while True:
   block=f.read(1024*1024)
   if not block:break
   h.update(block)
 return h.hexdigest()
def item(p,label):
 s=p.stat()
 return {'path':label,'bytes':s.st_size,'sha256':digest(p),'mode':oct(stat.S_IMODE(s.st_mode)),'resolved':str(p.resolve())}
out={'inputs':[],'target_libraries':[],'tools':[],'outputs':[],'errors':[]}
for kind,base,entries in [('inputs',root,request['inputs']),('target_libraries',tc,request['libraries'])]:
 for expected in entries:
  p=base/expected['path']
  if not p.is_file() or p.is_symlink():
   out['errors'].append('missing/nonregular '+str(p));continue
  got=item(p,expected['path']);out[kind].append(got)
  if any(got[k]!=expected[k] for k in ['bytes','sha256']):out['errors'].append('identity '+str(p))
  if kind=='inputs' and got['mode']!='0o444':out['errors'].append('source mode '+str(p))
tools=[Path(p) for p in request['tools']]+sorted((tc/'lib').glob('librustc_driver*.so'))
for p in tools:
 if not p.is_file():out['errors'].append('missing tool '+str(p));continue
 out['tools'].append(item(p,str(p)))
for p in sorted((root/'build').rglob('*')):
 if p.is_symlink():out['errors'].append('output symlink '+str(p))
 elif p.is_file():out['outputs'].append(item(p,str(p.relative_to(root))))
out['output_bytes']=sum(p['bytes'] for p in out['outputs'])
if out['output_bytes']>request['cap']:out['errors'].append('generated output cap exceeded')
print(json.dumps(out,indent=2))
sys.exit(2 if out['errors'] else 0)
'''


def write_capture(prefix, argv, timeout):
    started = time.monotonic()
    timed_out = False
    try:
        run = subprocess.run(argv, capture_output=True, timeout=timeout)
        code, stdout, stderr = run.returncode, run.stdout, run.stderr
    except subprocess.TimeoutExpired as exc:
        code, stdout, stderr = None, exc.stdout or b"", exc.stderr or b""
        timed_out = True
    (prefix.with_suffix(".stdout")).write_bytes(stdout)
    (prefix.with_suffix(".stderr")).write_bytes(stderr)
    receipt = {"argv": argv, "exit": code, "timed_out": timed_out,
               "elapsed_seconds": time.monotonic() - started,
               "stdout_sha256": hashlib.sha256(stdout).hexdigest(),
               "stderr_sha256": hashlib.sha256(stderr).hexdigest()}
    (prefix.with_suffix(".json")).write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt, stdout, stderr


def main():
    if len(sys.argv) != 2:
        raise SystemExit("Pass one immutable proposed compile-command ID")
    frozen = ROOT / "PREPARATION-FREEZE.json"
    if hashlib.sha256(frozen.read_bytes()).hexdigest() != "42a976cc612912f2729197658b28910e61dd931cd45fb80052e63143f3076df5":
        raise SystemExit("Reviewed preparation freeze identity changed")
    for e in json.loads(frozen.read_text())["files"]:
        if hashlib.sha256((ROOT / e["path"]).read_bytes()).hexdigest() != e["sha256"]:
            raise SystemExit("Reviewed preparation entry changed: " + e["path"])
    proposed = json.loads((ROOT / "commands-proposed.json").read_text())
    choices = [c for c in proposed["commands"] if c["stage"] == "compile" and c["id"] == sys.argv[1]]
    if len(choices) != 1:
        raise SystemExit("Not one of eight authorized compile commands")
    command = choices[0]
    captures = ROOT / "compile-static" / "captures-v3"
    captures.mkdir(parents=True, exist_ok=True)
    prefix = captures / command["id"]
    if prefix.with_suffix(".json").exists():
        raise SystemExit("Existing receipt: no implicit retry")
    staged = json.loads((BASE / "e46-staging-v3" / "staged-inputs.json").read_text())
    libraries = json.loads((BASE / "e46-runtime-preflight" / "ready-stdlib-inventory.stdout").read_text())
    request = {"inputs": staged["files"], "libraries": libraries,
               "toolchain": TC, "cap": CAP,
               "tools": [TC + "/bin/rustc", "/usr/bin/cc", "/usr/bin/ld",
                         "/usr/bin/objdump", "/usr/bin/readelf", "/usr/bin/timeout",
                         "/usr/bin/x86_64-linux-gnu-gcc", "/usr/bin/x86_64-linux-gnu-ld",
                         "/usr/bin/x86_64-linux-gnu-objdump", "/usr/bin/qemu-x86_64",
                         "/usr/x86_64-linux-gnu/lib/ld-linux-x86-64.so.2"]}
    snap_argv = [DOCKER, "exec", CID, "python3", "-c", SNAPSHOT, json.dumps(request)]
    before_receipt, before_stdout, _ = write_capture(captures / (command["id"] + "-before"), snap_argv, 60)
    if before_receipt["exit"] != 0:
        raise SystemExit("Before snapshot failed: no compiler started")
    before = json.loads(before_stdout)
    expected_tools = {}
    for line in (BASE / "e46-runtime-preflight" / "ready-tool-hashes.stdout").read_text().splitlines():
        digest, name = line.split(maxsplit=1)
        expected_tools[name.strip()] = digest
    actual_tools = {t["path"]: t["sha256"] for t in before["tools"]}
    if any(actual_tools.get(name) != digest for name, digest in expected_tools.items()):
        raise SystemExit("Parent tool identity disagreement: no compiler started")
    if len(before["tools"]) <= len(request["tools"]):
        raise SystemExit("No rustc driver library captured: diagnose before compile")
    env = dict(proposed["base_environment"])
    env.update(command["environment"])
    argv = [DOCKER, "exec", "--workdir", "/e46", CID, "/usr/bin/env", "-i"]
    argv += [key + "=" + value for key, value in sorted(env.items())]
    argv += ["/usr/bin/timeout", "--signal=TERM", "600s"] + command["argv"]
    receipt, stdout, stderr = write_capture(prefix, argv, 615)
    after_receipt, after_stdout, _ = write_capture(captures / (command["id"] + "-after"), snap_argv, 60)
    if after_receipt["exit"] != 0:
        raise SystemExit("After snapshot failed: stop dependent work")
    after = json.loads(after_stdout)
    unchanged = all(before[k] == after[k] for k in ["inputs", "target_libraries", "tools"])
    result = {"command_id": command["id"], "compiler_exit": receipt["exit"],
              "clean_streams": not stdout and not stderr,
              "inputs_libraries_tools_unchanged": unchanged,
              "source_files": len(after["inputs"]), "target_libraries": len(after["target_libraries"]),
              "tool_files": len(after["tools"]), "generated_bytes": after["output_bytes"],
              "subject_executed": False, "producer": "owned unverified capture helper"}
    (captures / (command["id"] + "-summary.json")).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))
    if receipt["exit"] != 0 or stdout or stderr or not unchanged:
        raise SystemExit("Compiler diagnostic/status/identity issue: stop before dependent phase")


if __name__ == "__main__":
    main()
