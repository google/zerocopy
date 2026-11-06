"""Bounded ELF64LE symbol importer and pinned literal comparison.

This is an unverified stdlib parser for this specimen, not HOL Light's loader.
It performs no native execution. Reassemble separately using assembly-log.json.
"""
import argparse
import hashlib
import json
from pathlib import Path
import struct


def symbol_bytes(blob, name):
    if len(blob) < 64:
        raise ValueError("truncated ELF header")
    header = struct.unpack_from("<16sHHIQQQIHHHHHH", blob)
    if header[0][:6] != b"\x7fELF\x02\x01" or header[1] != 1 or header[2] != 62:
        raise ValueError("requires relocatable x86_64 ELF64LE")
    shoff, shentsize, shnum = header[6], header[11], header[12]
    if shentsize != 64 or shoff + shnum * 64 > len(blob):
        raise ValueError("section header bounds")
    sections = [struct.unpack_from("<IIQQQQIIQQ", blob, shoff + 64 * i) for i in range(shnum)]
    found = []
    for section in sections:
        if section[1] != 2:
            continue
        if section[9] != 24 or section[6] >= len(sections):
            raise ValueError("symbol-table format")
        strings = sections[section[6]]
        strtab = blob[strings[4]:strings[4] + strings[5]]
        for offset in range(section[4], section[4] + section[5], 24):
            st_name, info, other, shndx, value, size = struct.unpack_from("<IBBHQQ", blob, offset)
            symbol = strtab[st_name:].split(b"\0", 1)[0].decode("ascii")
            if symbol != name:
                continue
            if info & 15 != 2 or shndx >= len(sections):
                raise ValueError("symbol is not a defined function")
            sec = sections[shndx]
            start = sec[4] + value
            if value + size > sec[5] or start + size > len(blob):
                raise ValueError("symbol bytes out of bounds")
            if any(s[1] in [4, 9] and s[7] == shndx and s[5] for s in sections):
                raise ValueError("code section has relocations")
            found.append((blob[start:start + size], start))
    if len(found) != 1:
        raise ValueError("expected exactly one named function")
    return found[0]


def validate(blob, expected, name="bignum_add"):
    code, offset = symbol_bytes(blob, name)
    if code != expected:
        raise ValueError("symbol bytes differ from proof literal")
    return code, offset


def run(path, literal_path):
    blob = path.read_bytes()
    literal = json.loads(literal_path.read_text())
    expected = bytes.fromhex(literal["bytes_hex"])
    code, offset = validate(blob, expected)
    mutations = {}
    patched = bytearray(blob)
    patched[offset + 4] ^= 1
    wrong_target = bytearray(blob)
    wrong_target[18:20] = (183).to_bytes(2, "little")
    for case, data, symbol in [("one_byte_patch", patched, "bignum_add"), ("wrong_target", wrong_target, "bignum_add"), ("wrong_symbol", blob, "missing")]:
        try:
            validate(data, expected, symbol)
        except ValueError as error:
            mutations[case] = {"rejected": True, "reason": str(error)}
        else:
            raise RuntimeError("mutation unexpectedly accepted: " + case)
    return {"object": path.name, "object_sha256": hashlib.sha256(blob).hexdigest(), "object_size": len(blob), "symbol": "bignum_add", "symbol_size": len(code), "symbol_file_offset": offset, "symbol_sha256": hashlib.sha256(code).hexdigest(), "symbol_hex": code.hex(), "matches_pinned_proof_literal": True, "negative_controls": mutations, "scope": "byte equality only; no HOL Light replay, instruction semantic proof, final linking, or native execution"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--object", type=Path, default=Path(__file__).with_name("bignum_add.o"))
    parser.add_argument("--literal", type=Path, default=Path(__file__).with_name("literal-bytes.json"))
    args = parser.parse_args()
    print(json.dumps(run(args.object, args.literal), indent=2))
