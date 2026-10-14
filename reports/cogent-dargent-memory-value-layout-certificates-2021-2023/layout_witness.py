#!/usr/bin/env python3
"""Finite relation witnesses. Does not execute Rust, Cogent, or Dargent."""
import json
from itertools import product


def get_field(word, field, swapped=False):
    slot = 1 - field if swapped else field
    return (word >> (2 * slot)) & 3


def set_field(word, field, value, swapped=False):
    slot = 1 - field if swapped else field
    mask = 3 << (2 * slot)
    return (word & ~mask) | (value << (2 * slot))


def check_family(swapped):
    roundtrip = True
    frame = True
    mismatch = None
    cases = 0
    for word, field, value in product(range(16), range(2), range(4)):
        updated = set_field(word, field, value, swapped)
        roundtrip &= get_field(updated, field, swapped) == value
        frame &= get_field(updated, 1 - field, swapped) == get_field(word, 1 - field, swapped)
        cases += 1
    for word, field in product(range(16), range(2)):
        expected = (word >> (2 * field)) & 3
        actual = get_field(word, field, swapped)
        if actual != expected and mismatch is None:
            mismatch = {"word": word, "field": field, "expected": expected, "actual": actual}
    return {"cases": cases, "roundtrip": roundtrip, "distinct_field_frame": frame,
            "independent_layout_agreement": mismatch is None, "first_mismatch": mismatch}


def main():
    expected = check_family(False)
    swapped = check_family(True)
    # A chosen abstraction preserves payload and forgets padding initializedness.
    # This is a relation witness, not a claim about any Rust transfer operation.
    before = {"payload": (7, True), "padding": (99, True)}
    after = {"payload": before["payload"], "padding": (None, False)}
    payload_decode = lambda state: state["payload"][0] if state["payload"][1] else None
    padding_readable = lambda state: state["padding"][1]
    transfer = {"payload_decode_agrees": payload_decode(before) == payload_decode(after),
                "padding_readable_before": padding_readable(before),
                "padding_readable_after": padding_readable(after)}
    assert expected["roundtrip"] and expected["distinct_field_frame"]
    assert expected["independent_layout_agreement"]
    assert swapped["roundtrip"] and swapped["distinct_field_frame"]
    assert not swapped["independent_layout_agreement"]
    assert swapped["first_mismatch"] == {"word": 1, "field": 0, "expected": 1, "actual": 0}
    assert transfer == {"payload_decode_agrees": True, "padding_readable_before": True,
                        "padding_readable_after": False}
    print(json.dumps({"scope": "complete enumeration of the defined 4-bit/two-field example",
                      "expected_accessors": expected, "swapped_accessors": swapped,
                      "chosen_transfer_abstraction": transfer}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
