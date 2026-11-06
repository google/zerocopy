"""Owned bounded thin-arm64 Mach-O byte importer. Not a verified loader.

Imports the eight bytes at the selected symbol, records section/address/relocation
facts, and emits Lean certificates for those concrete imported byte lists.
No mutated artifact is ever executed.
"""
from pathlib import Path
import hashlib
import json
import struct

EXPECTED = bytes.fromhex("00004039c0035fd6")
SYMBOL = "_read_byte_leaf"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_symbol(blob):
    require(len(blob) >= 32, "short Mach-O header")
    magic, cpu, _, kind, ncmds, command_size, _, _ = struct.unpack_from("<IiiIIIII", blob)
    require(magic == 0xfeedfacf and cpu == 0x100000c and kind in (1, 2), "unsupported Mach-O")
    limit = 32 + command_size
    require(limit <= len(blob), "load-command bounds")
    sections, symtab, pos = [], None, 32
    for _ in range(ncmds):
        require(pos + 8 <= limit, "short load command")
        command, size = struct.unpack_from("<II", blob, pos)
        require(size >= 8 and pos + size <= limit, "load-command size")
        if command == 0x19:
            require(size >= 72, "short segment")
            count = struct.unpack_from("<I", blob, pos + 64)[0]
            require(72 + count * 80 <= size, "section-table bounds")
            for index in range(count):
                q = pos + 72 + index * 80
                name, segment, address, length, offset, alignment, reloff, nreloc, flags = struct.unpack_from("<16s16sQQIIIII", blob, q)
                sections.append(dict(name=name.rstrip(b"\0").decode(), segment=segment.rstrip(b"\0").decode(),
                                     address=address, length=length, offset=offset, alignment=alignment,
                                     relocation_offset=reloff, relocation_count=nreloc, flags=flags))
        elif command == 2:
            require(size >= 24 and symtab is None, "symbol-table shape")
            symtab = struct.unpack_from("<IIII", blob, pos + 8)
        pos += size
    require(pos == limit and symtab is not None, "load-command/symbol-table identity")
    offset, count, strings, string_size = symtab
    require(offset + count * 16 <= len(blob) and strings + string_size <= len(blob), "symbol-table bounds")
    selected, symbols = None, []
    for index in range(count):
        ni, typ, si, _, value = struct.unpack_from("<IBBHQ", blob, offset + index * 16)
        require(ni < string_size, "string-table index")
        end = blob.find(b"\0", strings + ni, strings + string_size)
        require(end >= 0, "unterminated name")
        name = blob[strings + ni:end].decode()
        if (typ & 0x0e) == 0x0e and 1 <= si <= len(sections):
            symbols.append((name, si, value))
        if name == SYMBOL:
            require(selected is None and (typ & 0x0e) == 0x0e and 1 <= si <= len(sections), "selected symbol identity")
            selected = (si, value)
    require(selected is not None, "missing selected symbol")
    si, address = selected
    section = sections[si - 1]
    delta = address - section["address"]
    require(section["name"] == "__text" and section["segment"] == "__TEXT", "selected section")
    require(section["flags"] & 0x80000000, "section must carry pure-instruction attribute")
    require(0 <= delta and delta + 8 <= section["length"], "entry-slice section bounds")
    start = section["offset"] + delta
    require(start + 8 <= len(blob), "entry-slice file bounds")
    require(address % 4 == 0 and 0 <= address and address + 8 <= 2**63 - 1, "certificate layout range")
    relocation_addresses = []
    rstart, nr = section["relocation_offset"], section["relocation_count"]
    require(rstart + nr * 8 <= len(blob), "relocation-table bounds")
    for index in range(nr):
        first, second = struct.unpack_from("<II", blob, rstart + 8 * index)
        require(first & 0x80000000 == 0, "scattered relocation unsupported")
        relocation_addresses.append(first)
    require(not any(delta <= r < delta + 8 for r in relocation_addresses), "relocation overlaps leaf bytes")
    next_symbols = [(n, v) for n, s, v in symbols if s == si and v > address]
    next_symbol = min(next_symbols, key=lambda r: r[1]) if next_symbols else None
    code = blob[start:start + 8]
    return dict(symbol=SYMBOL, address=address, file_offset=start, imported_length=8,
                bytes=code.hex(), bytes_sha256=hashlib.sha256(code).hexdigest(), matches=code == EXPECTED,
                section=section, no_relocation_in_slice=True, next_symbol=next_symbol,
                slice_scope="8 bytes at entry; no claim that symbol extent equals8 or loader mapping is verified")


def python_accept(code):
    if len(code) != 8:
        return False
    first, second = struct.unpack("<II", code)
    # Independently executable presentation of the Lean field checker.
    if first % 1024 or first // 4194304 != 229 or second != 0xd65f03c0:
        return False
    return (first // 1024) % 4096 == 0


def bind_all(root):
    rows, lean = [], ["module", "public import Adapter", "@[expose] public section", "open CheckedByteLeaf"]
    for opt in (0, 3):
        for suffix in (".o", ""):
            name = f"artifacts/leaf-O{opt}{suffix}"
            blob = (root / name).read_bytes()
            result = read_symbol(blob)
            require(result["matches"] and python_accept(bytes.fromhex(result["bytes"])), "compiled byte disagreement")
            changed = bytearray(blob)
            changed[result["file_offset"]] ^= 1
            mutant = read_symbol(bytes(changed))
            require(not mutant["matches"] and not python_accept(bytes.fromhex(mutant["bytes"])), "mutant accepted")
            truncations = 0
            for truncated in (b"", blob[:31], blob[:40]):
                try:
                    read_symbol(truncated)
                except ValueError:
                    truncations += 1
                else:
                    raise ValueError("truncated importer accepted")
            row = dict(artifact=name, artifact_sha256=hashlib.sha256(blob).hexdigest(), artifact_length=len(blob),
                       binding=result, changed_byte_rejected=True, changed_artifact_sha256=hashlib.sha256(changed).hexdigest(),
                       truncated_files_rejected=truncations)
            rows.append(row)
            ident = f"O{opt}_{'object' if suffix else 'linked'}"
            literal = ",".join(str(x) for x in bytes.fromhex(result["bytes"]))
            changed_literal = ",".join(str(x) for x in bytes.fromhex(mutant["bytes"]))
            lean.extend([f"-- Artifact SHA256 {row['artifact_sha256']}; external importer file offset {result['file_offset']}.",
                         f"def bytes_{ident} : List UInt8 := [{literal}]",
                         f"theorem bound_{ident} : certificate {result['address']} bytes_{ident} = some (executable {result['address']} 0) := by rfl",
                         f"theorem mutation_{ident} : certificate {result['address']} [{changed_literal}] = none := by decide",
                         f"#print axioms bound_{ident}", f"#print axioms mutation_{ident}"])
    controls = 0
    for index in range(8):
        for replacement in range(256):
            if replacement == EXPECTED[index]:
                continue
            mutant = bytearray(EXPECTED)
            mutant[index] = replacement
            require(not python_accept(mutant), "single-byte mutant accepted")
            controls += 1
    (root / "support/BindingCertificates.lean").write_text("\n".join(lean) + "\n")
    output = dict(artifacts=rows, single_byte_mutants_rejected=controls,
                  parser_scope="owned bounded Mach-O importer, unverified; Lean checks concrete imported lists",
                  no_mutated_native_execution=True)
    (root / "logs/binding.json").write_text(json.dumps(output, indent=2) + "\n")
    return output


if __name__ == "__main__":
    result = bind_all(Path.cwd().resolve())
    print(json.dumps(dict(artifacts=len(result["artifacts"]),
                          single_byte_mutants_rejected=result["single_byte_mutants_rejected"], all_match=True)))
