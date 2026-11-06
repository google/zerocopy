"""Lexical observation of immutable selected files; not theorem dependency checking."""
import json
import re
import subprocess
import sys

REVISION = "0a83dba42db7ce0b445034ece5298afe980e57dc"
FILES = ("VfMir.v", "SymbolicExecution.v", "AxSem.v", "SymexSoundness.v")
rows = []
for name in FILES:
    path = "bin/rust/rocq/" + name
    result = subprocess.run(["git", "-C", sys.argv[1], "show", REVISION + ":" + path],
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode:
        raise SystemExit(f"Git object read failed for {path}: status {result.returncode}")
    text = result.stdout.decode("utf-8")
    rows.append({"file": name,
                 "admitted_tokens": len(re.findall(r"\bAdmitted\.", text)),
                 "axiom_declarations": len(re.findall(r"^Axiom\b", text, re.M)),
                 "parameter_declarations": len(re.findall(r"^Parameter\b", text, re.M)),
                 "storage_transition_lines": [i + 1 for i, line in enumerate(text.splitlines())
                                              if "StorageLive" in line or "StorageDead" in line]})
print(json.dumps({"repository": "verifast/verifast", "revision": REVISION,
                  "method": "lexical selected-file scan; not transitive assumption checking",
                  "files": rows}, indent=2))
