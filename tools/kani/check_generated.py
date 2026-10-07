#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Check compiled generated proofs, including attributes injected by other macros.

The __kani_contract_ name prefix is reserved for zerocopy-kani-macros. Ordinary
handwritten caller harnesses may use verified stubs; generated contract proofs
must execute implementations, without replacement stubs or expected panics.
"""

ATTRIBUTE_KEYS = {
    "kind", "should_panic", "solver", "unwind_value", "stubs", "verified_stubs",
}


def validate_generated(metadata):
    proofs = []
    for harness in metadata["proof_harnesses"] + metadata["test_harnesses"]:
        if not any(part.startswith("__kani_contract_") for part in
                   harness["pretty_name"].split("::")):
            continue
        attrs = harness["attributes"]
        if set(attrs) != ATTRIBUTE_KEYS:
            raise ValueError("unexpected generated proof metadata schema")
        kind = attrs["kind"]
        if not isinstance(kind, dict) or set(kind) != {"ProofForContract"}:
            raise ValueError("generated proof must verify a function contract")
        if attrs["should_panic"] or attrs["stubs"] or attrs["verified_stubs"]:
            raise ValueError("substitutions and expected panics are forbidden in generated proofs")
        if harness.get("contract", {}).get("recursion_tracker") is not None:
            raise ValueError("recursive contract assumptions are forbidden in generated proofs")
        if "{closure#" in harness["pretty_name"]:
            raise ValueError("generated proof was nested inside a contracted function")
        proofs.append(harness["pretty_name"])
    if len(proofs) != len(set(proofs)):
        raise ValueError("duplicate generated contract proof")
    return proofs
