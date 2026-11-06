"""Metadata tools only. No native image invocation or mutation."""
import json
from pathlib import Path
from capture_stage import ROOT, run, sha


def main():
    identities = json.loads((ROOT / "tool-identities.json").read_text())
    for entry in identities["files"]:
        if sha(Path(entry["path"]).read_bytes()) != entry["sha256"]:
            raise ValueError("stop: inspected tool identity changed")
    bind = json.loads((ROOT / "compile-outputs.json").read_text())
    for entry in bind["outputs"]:
        if sha((ROOT / entry["path"]).read_bytes()) != entry["sha256"]:
            raise ValueError("stop: positive artifact changed")
    tools = Path("/Library/Developer/CommandLineTools/usr/bin")
    objdump = str(tools / "llvm-objdump")
    dwarf = str(tools / "llvm-dwarfdump")
    for stem, artifact in [("object", "build/specimen.o"), ("image", "build/specimen")]:
        run(stem + "-unwind", [objdump, "--macho", "--unwind-info", artifact])
        run(stem + "-eh-frame", [dwarf, "--eh-frame", artifact])
        run(stem + "-bounce-disassembly", [objdump, "--macho", "--disassemble", "--dis-symname", "_anneal_unwind_bounce", artifact])
        run(stem + "-symbols", [str(tools / "nm"), "-n", "-m", artifact])
    run("object-relocations", [objdump, "--reloc", "build/specimen.o"])
    run("image-loadcommands", [str(tools / "otool"), "-l", "build/specimen"])
    run("image-dylibs", [str(tools / "otool"), "-L", "build/specimen"])
    print("metadata captures complete; native image NOT executed")


if __name__ == "__main__":
    main()
