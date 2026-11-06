#!/usr/bin/env python3
"""Original finite witness; does not execute or verify an upstream tool."""
import json
from itertools import product


OUTCOMES = ('ub', 'poison', 0, 1)


def refines(source, target):
    if source == 'ub':
        return True
    if source == 'poison':
        return target != 'ub'
    return target == source


def target_policy(outcome):
    return outcome in (0, 1)


def source_failure(outcome):
    return outcome == 'ub'


def source_function(n):
    return n


def target_function(n):
    return n if n < 4 else n + 1


def main():
    accepted = [(s, t) for s, t in product(OUTCOMES, repeat=2) if refines(s, t)]
    assertions = {
        'source_ub_refines_to_defined_target': refines('ub', 0),
        'source_failure_not_reflected_by_safe_refined_target': any(
            source_failure(s) and not source_failure(t) for s, t in accepted),
        'defined_source_cannot_refine_to_wrong_value': not refines(0, 1),
        'poison_source_cannot_refine_to_immediate_ub': not refines('poison', 'ub'),
        'weak_target_policy_accepts_wrong_functional_result': any(
            target_policy(s) and target_policy(t) and not refines(s, t)
            for s, t in product(OUTCOMES, repeat=2)),
        'restricted_input_check_misses_later_difference': all(
            source_function(n) == target_function(n) for n in range(4))
            and source_function(4) != target_function(4),
    }
    assert len(accepted) == 9
    assert all(assertions.values())
    print(json.dumps({
        'scope': 'original four-outcome semantics and five-input illustration; no upstream proof',
        'outcomes': list(OUTCOMES),
        'pairs_checked': 16,
        'accepted_pairs': accepted,
        'assertions': assertions,
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
