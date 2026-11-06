"""One discriminating host-only control for the retained CUDF audit."""
import sys
sys.dont_write_bytecode=True
import json,pathlib
from audit_cudf import audit

if len(sys.argv)!=3:raise SystemExit('false_solution_control.py CUDF NATIVE_JSON')
cudf,native=map(pathlib.Path,sys.argv[1:])
data=json.loads(native.read_text())
selection={(x['install']['name'],x['install']['version']) for x in data['solution']}
selection.remove(('coq-iris','dev.2024-09-10.1.6f24ed4b'))
try:
    audit(cudf,native,selection)
except ValueError as error:
    if not str(error).startswith('unsatisfied dependency'):raise
    print(json.dumps({'status':'EXPECTED_REJECTION','reason':str(error)},indent=2))
else:
    raise RuntimeError('false solution accepted')
