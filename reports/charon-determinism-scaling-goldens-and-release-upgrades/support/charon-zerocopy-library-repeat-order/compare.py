#!/usr/bin/env python3
"""Compare raw LLBC with only run-path and short_names order accounted for."""
import hashlib
import json
import argparse
from pathlib import Path

KEY = b'"short_names":'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def array_end(data, start):
    assert data[start] == 91
    depth, quoted, escaped = 0, False, False
    for i in range(start, len(data)):
        c = data[i]
        if quoted:
            if escaped:
                escaped = False
            elif c == 92:
                escaped = True
            elif c == 34:
                quoted = False
        elif c == 34:
            quoted = True
        elif c == 91:
            depth += 1
        elif c == 93:
            depth -= 1
            if depth == 0:
                return i + 1
    raise ValueError("unterminated short_names array")


def examine(root, n):
    path = root / f"run{n}/zerocopy.llbc"
    data = path.read_bytes()
    assert data.count(KEY) == 1
    start = data.index(KEY) + len(KEY)
    end = array_end(data, start)
    names = json.loads(data[start:end])
    encoded = [json.dumps(x, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode() for x in names]
    keys = [json.dumps(x["key"], sort_keys=True, separators=(",", ":")) for x in names]
    old = f"/run{n}/zerocopy.llbc".encode()
    new = b"/runX/zerocopy.llbc"
    assert data.count(old) == 1
    assert len(old) == len(new)
    assert data.endswith(b'"has_errors":true}')
    normalized = data[:start] + data[end:]
    normalized = normalized.replace(old, new)
    return {
        "raw_sha256": sha(data),
        "raw_bytes": len(data),
        "short_names_offset": start,
        "short_names_bytes": end - start,
        "short_names_entries": len(names),
        "short_names_unique_keys": len(set(keys)),
        "short_names_order_sha256": sha(b"\n".join(encoded)),
        "short_names_multiset_sha256": sha(b"\n".join(sorted(encoded))),
        "non_short_names_path_normalized_sha256": sha(normalized),
        "has_errors": True,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("work", type=Path, help="directory containing run1..run3 raw LLBC")
    parser.add_argument("--expected", type=Path, help="retained comparison: verify path-independent fields")
    args = parser.parse_args()
    result = {f"run{n}": examine(args.work, n) for n in (1, 2, 3)}
    result["checks"] = {
        "same_length": len({r["raw_bytes"] for r in result.values()}) == 1,
        "same_short_names_members": len({r["short_names_multiset_sha256"] for r in result.values()}) == 1,
        "same_other_bytes_after_path_normalization": len({r["non_short_names_path_normalized_sha256"] for r in result.values()}) == 1,
        "different_short_names_order": len({r["short_names_order_sha256"] for r in result.values()}) > 1,
        "unique_short_names_keys": all(r["short_names_entries"] == r["short_names_unique_keys"] for r in result.values()),
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    assert all(result["checks"].values())
    if args.expected:
        expected = json.loads(args.expected.read_text())
        assert result["checks"] == expected["checks"]
        for n in (1, 2, 3):
            key = f"run{n}"
            for field in ("short_names_entries", "short_names_unique_keys",
                          "short_names_multiset_sha256", "has_errors"):
                assert result[key][field] == expected[key][field], (key, field)


if __name__ == "__main__":
    main()
