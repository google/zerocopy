"""Bounded reader for this experiment's thin little-endian Mach-O64 files.

This is an owned data-binding probe, not a verified loader or ISA decoder.
"""
import hashlib
import json
from pathlib import Path
import struct
import sys

EXPECTED = {"_naked_add": bytes.fromhex("0000018bc0035fd6"),
            "_naked_store": bytes.fromhex("010000f9c0035fd6")}

def functions(blob, wanted):
    if len(blob) < 32:
        raise ValueError("short header")
    magic, cpu, _, _, ncmds, cmdsize, _, _ = struct.unpack_from("<IiiIIIII", blob)
    if magic != 0xfeedfacf or cpu != 0x100000c:
        raise ValueError("only thin little-endian arm64 Mach-O64 is admitted")
    if 32 + cmdsize > len(blob):
        raise ValueError("load command range")
    sections = []
    symtab = None
    pos = 32
    for _ in range(ncmds):
        if pos + 8 > 32 + cmdsize:
            raise ValueError("short load command")
        cmd, size = struct.unpack_from("<II", blob, pos)
        if size < 8 or pos + size > 32 + cmdsize:
            raise ValueError("load command size")
        if cmd == 0x19:
            if size < 72:
                raise ValueError("short segment")
            nsects = struct.unpack_from("<I", blob, pos + 64)[0]
            if 72 + nsects * 80 > size:
                raise ValueError("short sections")
            for i in range(nsects):
                q = pos + 72 + i * 80
                sect, seg, addr, length, offset = struct.unpack_from("<16s16sQQI", blob, q)
                sections.append({"name":sect.rstrip(b"\0").decode(),
                                 "segment":seg.rstrip(b"\0").decode(),
                                 "address":addr, "length":length, "offset":offset})
        elif cmd == 2:
            if size < 24 or symtab is not None:
                raise ValueError("symbol table shape")
            symtab = struct.unpack_from("<IIII", blob, pos + 8)
        pos += size
    if pos != 32 + cmdsize or symtab is None:
        raise ValueError("load command/symbol table mismatch")
    off, count, strings, string_size = symtab
    if off + count * 16 > len(blob) or strings + string_size > len(blob):
        raise ValueError("symbol table bounds")
    result = {}
    for i in range(count):
        name_i, typ, sec_i, _, value = struct.unpack_from("<IBBHQ", blob, off + i * 16)
        if name_i >= string_size:
            raise ValueError("string index")
        end = blob.find(b"\0", strings + name_i, strings + string_size)
        if end < 0:
            raise ValueError("unterminated symbol")
        name = blob[strings + name_i:end].decode()
        if name not in wanted:
            continue
        if name in result or (typ & 0x0e) != 0x0e or not 1 <= sec_i <= len(sections):
            raise ValueError("symbol identity/section")
        sec = sections[sec_i - 1]
        length = len(wanted[name])
        delta = value - sec["address"]
        if sec["name"] != "__text" or sec["segment"] != "__TEXT" or not 0 <= delta <= sec["length"] - length:
            raise ValueError("function range")
        start = sec["offset"] + delta
        if start + length > len(blob):
            raise ValueError("file range")
        data = blob[start:start + length]
        result[name] = {"file_offset":start,"address":value,"bytes":data.hex(),
                        "matches":data == wanted[name],"sha256":hashlib.sha256(data).hexdigest()}
    if set(result) != set(wanted):
        raise ValueError("missing selected function")
    return result

def main():
    rows=[]
    for name in sys.argv[1:]:
        p=Path(name);b=p.read_bytes();r=functions(b,EXPECTED)
        if not all(x['matches'] for x in r.values()):
            raise SystemExit("selected byte mismatch")
        mutated=bytearray(b);mutated[r['_naked_add']['file_offset']] ^= 1
        changed=functions(bytes(mutated),EXPECTED)
        if changed['_naked_add']['matches']:
            raise SystemExit("byte mutation was not rejected")
        for bad in [b'',b[:31],b[:40]]:
            try: functions(bad,EXPECTED)
            except ValueError: pass
            else: raise SystemExit("truncation accepted")
        wrong=dict(EXPECTED);wrong['_naked_add']=EXPECTED['_naked_store']
        if functions(b,wrong)['_naked_add']['matches']:
            raise SystemExit('wrong expected function accepted')
        rows.append({'artifact':p.name,'artifact_sha256':hashlib.sha256(b).hexdigest(),
                     'functions':r,'byte_mutant_rejected':True,'truncations_rejected':3,
                     'wrong_function_rejected':True})
    print(json.dumps(rows,indent=2))

if __name__ == '__main__': main()
