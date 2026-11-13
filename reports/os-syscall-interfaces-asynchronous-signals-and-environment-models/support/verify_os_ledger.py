#!/usr/bin/env python3
"""Verify os_environment_assumption_ledger.json structure and entries."""

from __future__ import annotations
import argparse
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ledger", type=Path, required=True)
    args = parser.parse_args()
    data = json.loads(args.ledger.read_text(encoding="utf-8"))
    assert len(data["linux_syscall_abi_table"]) == 3
    assert len(data["platform_os_reachability"]) == 3
    assert len(data["environment_assumption_ledger_entries"]) == 5
    print("OK: verified 3 Linux ISA syscall ABIs, 3 OS reachability entries, and 5 assumption ledger entries.")


if __name__ == "__main__":
    main()
