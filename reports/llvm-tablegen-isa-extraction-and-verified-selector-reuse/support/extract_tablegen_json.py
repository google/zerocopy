#!/usr/bin/env python3
"""Extract instruction, pattern, register class, feature, and CPU tables from llvm-tblgen --dump-json."""
import argparse
import json
import subprocess
from collections import Counter
from pathlib import Path

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--llvm-tblgen", default="llvm-tblgen")
    ap.add_argument("--llvm-root", required=True, type=Path)
    ap.add_argument("--target", choices=["X86", "AArch64", "RISCV"], required=True)
    args = ap.parse_args()

    td_file = args.llvm_root / "lib/Target" / args.target / f"{args.target}.td"
    inc_dir = args.llvm_root / "lib/Target" / args.target
    res = subprocess.run(
        [args.llvm_tblgen, "--dump-json", "-I", str(args.llvm_root / "include"), "-I", str(inc_dir), str(td_file)],
        capture_output=True, text=True, check=True
    )
    data = json.loads(res.stdout)
    inst_of = data.get("!instanceof", {})
    insts = inst_of.get("Instruction", [])
    pseudo_or_cg = sum(1 for i in insts if data[i].get("isPseudo") == 1 or data[i].get("isCodeGenOnly") == 1)
    print(json.dumps({
        "target": args.target,
        "total_records": len([k for k in data if not k.startswith("!")]),
        "instructions_total": len(insts),
        "instructions_encodable": len(insts) - pseudo_or_cg,
        "patterns": len(inst_of.get("Pattern", [])),
        "registers": len(inst_of.get("Register", [])),
        "register_classes": len(inst_of.get("RegisterClass", [])),
        "subtarget_features": len(inst_of.get("SubtargetFeature", [])),
        "processors": len(inst_of.get("Processor", [])),
        "sched_models": len(inst_of.get("SchedMachineModel", [])),
    }, indent=2))

if __name__ == "__main__":
    main()
