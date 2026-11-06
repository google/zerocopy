"""Extract constructor inventory, not semantic or encoding support coverage."""
import argparse
import json
from pathlib import Path
import re


def constructors(text, name):
    body = text.split("inductive " + name, 1)[1]
    body = re.split(r"\n(?:inductive|structure|namespace|abbrev|def)\b", body, maxsplit=1)[0]
    return re.findall(r"^\s+\|\s+(\w+)", body, re.MULTILINE)


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("kraken_source", type=Path)
    args = p.parse_args()
    out = {"revision": "8af78062037bc237b341d20252aafd1797c1bcb7", "scope": "syntax constructors only; parameter/encoding/semantics constraints not inferred"}
    for arch in ["X64", "AArch64"]:
        syntax = (args.kraken_source / "Kraken" / arch / "Syntax.lean").read_text()
        semantics = (args.kraken_source / "Kraken" / arch / "Semantics.lean").read_text()
        out[arch] = {"operations": constructors(syntax, "Operation"), "effects": constructors(semantics, "Effects")}
        if arch == "X64":
            out[arch]["vector_operations"] = constructors(syntax, "AvxOperation")
    print(json.dumps(out, indent=2))
