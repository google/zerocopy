"""PREPARATION ONLY; literal finite guard, not a complete OCaml parser."""
import re,sys
from pathlib import Path
s=Path(sys.argv[1]).read_text()
if re.search(r'\blet\s+(?:rec\s+)?check_axioms\b',s):
    raise SystemExit('ANNEAL_FORBIDDEN_CHECKER_DEFINITION')
print('ANNEAL_LITERAL_CHECKER_GUARD_PASS')
