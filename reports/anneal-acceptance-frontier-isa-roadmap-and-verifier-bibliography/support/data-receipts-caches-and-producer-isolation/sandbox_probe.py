"""Owned, bounded sandbox control. Does not run submitted producer code."""
from pathlib import Path
import subprocess
import tempfile
import json
import hashlib
import os
import sys

root = Path(__file__).resolve().parent
with tempfile.TemporaryDirectory(prefix="producer-boundary-", dir=root) as temp:
    base = Path(temp)
    producer = base / "producer"
    protected = base / "protected"
    producer.mkdir()
    protected.mkdir()
    challenge = protected / "challenge.json"
    challenge.write_text('{"claim":"source-safe","generation":1}\n')
    before = hashlib.sha256(challenge.read_bytes()).hexdigest()
    code = '''from pathlib import Path
import json,sys
out=Path(sys.argv[1]); challenge=Path(sys.argv[2])
out.write_text("producer output\\n")
try:
 challenge.write_text("changed claim\\n")
 result="write succeeded"
except OSError as error:
 result={"exception":type(error).__name__,"errno":error.errno}
print(json.dumps({"producer_output":out.exists(),"protected_write":result}))
'''
    subject = base / "producer.py"
    subject.write_text(code)
    profile = '(version 1) (allow default) (deny network*) (deny file-write*) (allow file-write* (subpath ' + json.dumps(str(producer)) + '))'
    command = ["/usr/bin/sandbox-exec", "-p", profile, sys.executable, "-I", str(subject), str(producer / "out.txt"), str(challenge)]
    result = subprocess.run(command, cwd=base, capture_output=True, timeout=20,
        env={"PATH":"/usr/bin:/bin:/opt/homebrew/bin", "PYTHONDONTWRITEBYTECODE":"1"})
    record = {
        "scope":"Specific owned producer process, write protection, no confidentiality or deployed Anneal containment claim",
        "exit":result.returncode,
        "stdout":result.stdout.decode(errors="replace"),
        "stderr":result.stderr.decode(errors="replace"),
        "protected_input_unchanged":hashlib.sha256(challenge.read_bytes()).hexdigest() == before,
        "producer_subject_sha256":hashlib.sha256(subject.read_bytes()).hexdigest(),
        "profile_pattern":"allow default; deny network; deny file writes except task-owned producer output",
        "sandbox_executable_sha256":hashlib.sha256(Path(command[0]).read_bytes()).hexdigest(),
        "python_executable_sha256":hashlib.sha256(Path(command[3]).read_bytes()).hexdigest(),
        "expected_security_result":"Successful producer write, denied challenge write, challenge unchanged",
    }
    (root / "sandbox-results.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record))
