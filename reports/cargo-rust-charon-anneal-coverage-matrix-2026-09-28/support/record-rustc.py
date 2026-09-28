#!/usr/bin/env python3
import json, os, subprocess, sys
from pathlib import Path
args=sys.argv[1:]
record={"argv":args,"cwd":os.getcwd(),"env":{k:os.environ.get(k) for k in ("CARGO_CRATE_NAME","CARGO_MANIFEST_DIR","CARGO_PKG_NAME","CARGO_PRIMARY_PACKAGE","OUT_DIR","HOST","TARGET","PROFILE","OPT_LEVEL","DEBUG","RUSTC_WORKSPACE_WRAPPER") if k in os.environ}}
with open(os.environ["PROBE_RUSTC_LOG"],"a") as f:
 f.write(json.dumps(record,sort_keys=True)+"\n")
os.execvp(args[0],args)
