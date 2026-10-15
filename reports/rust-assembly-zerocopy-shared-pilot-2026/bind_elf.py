#!/usr/bin/env python3
"""Owned unverified ELF64-LE data reader, not an ISA decoder/proof.

Bind actual function bytes, symbol identities and the one hand-written helper
call relocation. Cross-check extracted bytes against captured GNU objdump.
Never run/link/load any artifact and never modify artifact bytes.
"""
from pathlib import Path
import hashlib
import json
import re
import struct

ROOT = Path(__file__).resolve().parent / "compile-static"
WHOLE = ["pilot_mul", "pilot_add128", "pilot_bswap", "pilot_load", "pilot_store",
         "pilot_copy16", "pilot_ptr", "pilot_call_helper", "pilot_simd_copy16", "pilot_simd_add16"]
INLINE = ["inline_carry", "inline_label", "inline_load", "inline_store"]
ZC = ["zc_decode", "zc_encode", "zc_copy16"]
RUST = ["rust_mul", "rust_add128", "rust_carry", "rust_swap", "rust_load", "rust_store",
        "rust_copy16", "rust_ptr", "rust_label", "rust_add16", "rust_call_helper"]


class ELF:
    def __init__(self, path):
        self.path, self.raw = path, path.read_bytes()
        b = self.raw
        if b[:6] != b"\x7fELF\x02\x01":
            raise SystemExit("Unsupported ELF class/encoding")
        self.kind, self.machine = struct.unpack_from("<HH", b, 16)
        off = struct.unpack_from("<Q", b, 40)[0]
        size, count, names = struct.unpack_from("<HHH", b, 58)
        if size != 64 or not count or count > 10000 or names >= count or off + size * count > len(b):
            raise SystemExit("Unsupported/truncated ELF section header form")
        self.sections = []
        for i in range(count):
            values = struct.unpack_from("<IIQQQQIIQQ", b, off + i * size)
            self.sections.append(dict(zip(["name_off", "type", "flags", "addr", "offset", "size",
                                           "link", "info", "align", "entry"], values)))
        strings = self.section_bytes(names)
        for s in self.sections:
            s["name"] = self.cstring(strings, s["name_off"])
        self.symbol_tables = {}
        for i, s in enumerate(self.sections):
            if s["type"] not in (2, 11):
                continue
            if s["entry"] != 24 or s["size"] % 24:
                raise SystemExit("Unsupported symbol entry form")
            names_raw = self.section_bytes(s["link"])
            symbols = []
            for at in range(s["offset"], s["offset"] + s["size"], 24):
                name, info, other, shndx, value, length = struct.unpack_from("<IBBHQQ", b, at)
                symbols.append({"name": self.cstring(names_raw, name), "info": info,
                                "section": shndx, "value": value, "size": length})
            self.symbol_tables[i] = symbols
        full = [syms for i, syms in self.symbol_tables.items() if self.sections[i]["type"] == 2]
        if len(full) != 1:
            raise SystemExit("Require one full symtab")
        self.symbols = full[0]

    @staticmethod
    def cstring(data, at):
        end = data.find(b"\0", at)
        if end < at:
            raise SystemExit("Unterminated ELF string")
        return data[at:end].decode("utf-8")

    def section_bytes(self, i):
        s = self.sections[i]
        if s["type"] == 8 or s["offset"] + s["size"] > len(self.raw):
            raise SystemExit("No file bytes for this section")
        return self.raw[s["offset"]:s["offset"] + s["size"]]

    def lookup(self, name, rust=False):
        if rust:
            matches = [s for s in self.symbols if s["name"].startswith("_ZN14extended_pilot")
                       and (str(len(name)) + name + "17h") in s["name"] and s["size"]]
        else:
            matches = [s for s in self.symbols if s["name"] == name and s["size"]]
        if len(matches) > 1:
            raise SystemExit("Ambiguous function " + name)
        return matches[0] if matches else None

    def function(self, s):
        sec = self.sections[s["section"]]
        relative = s["value"] - sec["addr"]
        if relative < 0 or relative + s["size"] > sec["size"] or not sec["flags"] & 4:
            raise SystemExit("Function outside executable section")
        start = sec["offset"] + relative
        return self.raw[start:start + s["size"]], start

    def relocs_in(self, symbol):
        out = []
        for sec in self.sections:
            if sec["type"] != 4 or sec["info"] != symbol["section"]:
                continue
            if sec["entry"] != 24:
                raise SystemExit("Unsupported RELA entry")
            for at in range(sec["offset"], sec["offset"] + sec["size"], 24):
                offset, info, addend = struct.unpack_from("<QQq", self.raw, at)
                if symbol["value"] <= offset < symbol["value"] + symbol["size"]:
                    target = self.symbol_tables[sec["link"]][info >> 32]
                    out.append({"offset_in_function": offset - symbol["value"],
                                "type": info & 0xffffffff, "target": target["name"], "addend": addend})
        return out


def disassembly_blocks(text):
    matches = list(re.finditer(r"^([0-9a-f]+) <(.+)>:\n", text, re.M))
    return {m.group(2): text[m.start():matches[i + 1].start() if i + 1 < len(matches) else len(text)]
            for i, m in enumerate(matches)}


def objdump_bytes(block, arch):
    out = bytearray()
    for line in block.splitlines()[1:]:
        match = re.match(r"\s*[0-9a-f]+:\s*\t([0-9a-f ]+)(?:\t|$)", line)
        if match:
            fields = match.group(1).split()
            if arch == "aarch64":
                out += b"".join(bytes.fromhex(x)[::-1] for x in fields)
            else:
                out += bytes.fromhex("".join(fields))
    return bytes(out)


def main():
    results = []
    for arch, machine in [("aarch64", 183), ("x86_64", 62)]:
        for opt in [0, 3]:
            directory = ROOT / "artifacts/build" / arch / ("O" + str(opt))
            obj, image = ELF(directory / "pilot.o"), ELF(directory / "pilot")
            if (obj.kind, image.kind, obj.machine, image.machine) != (1, 3, machine, machine):
                raise SystemExit("ELF type/target mismatch")
            dis = {kind: disassembly_blocks((ROOT / "inspection" / f"{arch}-O{opt}-{kind}-disassembly.stdout").read_text())
                   for kind in ["object", "image"]}
            rows, excerpts, missing = [], [], []
            for name in WHOLE + ["pilot_helper"] + INLINE + ZC + RUST:
                is_rust = name in INLINE + ZC + RUST
                pair = []
                for kind, elf in [("object", obj), ("image", image)]:
                    symbol = elf.lookup(name, is_rust)
                    if symbol is None:
                        missing.append({"name": name, "artifact": kind})
                        pair.append(None)
                        continue
                    body, file_at = elf.function(symbol)
                    label = "extended_pilot::" + name if is_rust else name
                    if label not in dis[kind]:
                        raise SystemExit("Function header missing from objdump " + label)
                    block = dis[kind][label]
                    extracted = objdump_bytes(block, arch)[:len(body)]
                    if body != extracted:
                        raise SystemExit("ELF/objdump byte disagreement " + arch + "/" + kind + "/" + name)
                    excerpts.append("\n### " + kind + ": " + label + "\n" + block)
                    pair.append({"symbol": symbol, "file_offset": file_at, "bytes": len(body),
                                 "hex": body.hex(), "sha256": hashlib.sha256(body).hexdigest()})
                row = {"name": name, "object": pair[0], "image": pair[1]}
                if name in WHOLE:
                    if not all(pair):
                        raise SystemExit("Required whole function absent")
                    old, _ = obj.function(pair[0]["symbol"])
                    new, _ = image.function(pair[1]["symbol"])
                    relocs = obj.relocs_in(pair[0]["symbol"])
                    row["relocations"] = relocs
                    if name != "pilot_call_helper":
                        if relocs or old != new:
                            raise SystemExit("Unexplained whole-function relocation/change")
                        row["object_linked_exact_bytes"] = True
                    else:
                        if len(relocs) != 1 or relocs[0]["target"] != "pilot_helper":
                            raise SystemExit("Unexpected hand-written call relocation")
                        rel = relocs[0]; target = image.lookup("pilot_helper")["value"]
                        pos = pair[1]["symbol"]["value"] + rel["offset_in_function"]
                        field = (target + rel["addend"] - pos)
                        patched = bytearray(old); off = rel["offset_in_function"]
                        if arch == "aarch64" and rel["type"] == 283 and rel["addend"] == 0 and field % 4 == 0:
                            word = struct.unpack_from("<I", old, off)[0]
                            struct.pack_into("<I", patched, off, (word & 0xfc000000) | ((field // 4) & 0x3ffffff))
                            decoded_target = pos + (((struct.unpack_from("<I", new, off)[0] & 0x3ffffff) ^ 0x2000000) - 0x2000000) * 4
                        elif arch == "x86_64" and rel["type"] == 4 and rel["addend"] == -4:
                            struct.pack_into("<i", patched, off, field)
                            decoded_target = pos + 4 + struct.unpack_from("<i", new, off)[0]
                        else:
                            raise SystemExit("Unsupported call relocation")
                        if bytes(patched) != new or decoded_target != target:
                            raise SystemExit("Call relocation/target disagreement")
                        row["call_target"] = target
                        row["object_linked_bytes_differ_only_by_checked_call_relocation"] = True
                rows.append(row)
            (ROOT / f"selected-{arch}-O{opt}.txt").write_text("".join(excerpts))
            results.append({"arch": arch, "opt": opt, "object_sha256": hashlib.sha256(obj.raw).hexdigest(),
                            "image_sha256": hashlib.sha256(image.raw).hexdigest(), "functions": rows, "missing_named_rust_functions": missing})
    (ROOT / "function-bindings.json").write_text(json.dumps({"status": "static-data-only", "subject_executed": False,
        "reader": "owned unverified ELF64LE parser, cross-checked with captured GNU objdump",
        "limits": "Not an ISA decoder/reference semantics theorem or compiler proof; Rust function relocation bodies are hashed, not universally validated.",
        "images": results}, indent=2) + "\n")
    print(json.dumps({"images": len(results), "whole_function_pairs_checked": 40,
                      "function_records": sum(len(r["functions"]) for r in results),
                      "missing_named_rust_functions": [{"arch": r["arch"], "opt": r["opt"], "missing": r["missing_named_rust_functions"]} for r in results if r["missing_named_rust_functions"]]}))


if __name__ == "__main__":
    main()
