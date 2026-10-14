"""Executable finite-memory countermodels to a final-state-only frame rule.

No actual assembly, Rust, upstream prover, or target hardware is executed.
"""
import json


def run_case(ops):
    initial = {0: 0, 8: 77, 16: 9}
    mem = initial.copy()
    trace = []
    for kind, addr, width, value in ops:
        trace.append({"kind": kind, "addr": addr, "width": width})
        for offset in range(width):
            if kind == "read":
                _ = mem.get(addr + offset, 0)
            else:
                mem[addr + offset] = value
    frame = all(mem.get(a, 0) == initial.get(a, 0) for a in set(mem) | set(initial) if a != 0)
    trace_safe = all(all(t["addr"] + i == 0 for i in range(t["width"])) for t in trace)
    return {"final_frame": frame, "trace_safe": trace_safe, "trace": trace}


def validate_coverage(reference, candidate):
    # Exact finite two-input trace relation; an omitted branch cannot be hidden.
    return all(reference[secret] == candidate.get(secret) for secret in [False, True])


def run():
    cases = {
        "positive_bounded_write": run_case([("write", 0, 1, 42)]),
        "out_of_range_read": run_case([("read", 8, 1, None)]),
        "forbidden_write_restore": run_case([("write", 8, 1, 99), ("write", 8, 1, 77)]),
        "crossing_width": run_case([("read", 0, 2, None)]),
    }
    assert cases["positive_bounded_write"]["trace_safe"]
    assert all(cases[name]["final_frame"] and not cases[name]["trace_safe"] for name in cases if name != "positive_bounded_write")
    reference = {False: [("read", 0, 1)], True: [("read", 8, 1)]}
    omitted = {False: [("read", 0, 1)]}
    missing_access = {False: [("read", 0, 1)], True: []}
    coverage = {"positive": validate_coverage(reference, reference), "omitted_branch": validate_coverage(reference, omitted), "omitted_access": validate_coverage(reference, missing_access)}
    assert coverage == {"positive": True, "omitted_branch": False, "omitted_access": False}
    return {"scope": "owned finite countermodels, not an upstream safety or constant-time theorem", "cases": cases, "finite_trace_validation": coverage, "secret_independent_addresses": reference[False] == reference[True]}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
