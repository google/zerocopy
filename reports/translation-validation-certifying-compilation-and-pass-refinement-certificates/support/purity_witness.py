#!/usr/bin/env python3
"""Reduced source-definition witness; not execution of PIR or Coq.

These cases reflect Value.dec_value' and Purity's pure-binding value rule
at basetunnel/2022-scp-translation-relations@72e619f3243498a612d8c6c5090b88117c404489.
The execution outcomes are illustrative and explicitly separate.
"""
import json


def reduced_dec_value(constructor):
    return constructor in {'Error', 'Constant', 'LamAbs'}


def reduced_dec_strict_purity(constructor):
    return reduced_dec_value(constructor)


def reduced_strict_purity_relation(constructor):
    return reduced_dec_value(constructor) and constructor != 'Error'


def main():
    cases = [
        {'constructor': c, 'checker_accepts_strict_binding': reduced_dec_strict_purity(c),
         'purity_relation_has_value_constructor': reduced_strict_purity_relation(c)}
        for c in ['Error', 'Constant', 'LamAbs']
    ]
    discrepancy = [c for c in cases if c['checker_accepts_strict_binding'] and
                   not c['purity_relation_has_value_constructor']]
    assert discrepancy == [{'constructor': 'Error', 'checker_accepts_strict_binding': True,
                            'purity_relation_has_value_constructor': False}]
    for case in cases[1:]:
        assert case['checker_accepts_strict_binding'] and case['purity_relation_has_value_constructor']
    # Chosen strict-let semantics: evaluate binding before the constant body.
    # This is not a reproduced PIR semantics implementation.
    source_outcome = 'error'
    deleted_target_outcome = 'ok(1)'
    assert source_outcome != deleted_target_outcome
    print(json.dumps({'scope': 'three-constructor reduced checker/predicate witness',
                      'source_revision': '72e619f3243498a612d8c6c5090b88117c404489',
                      'fresh_coq_check': False, 'cases': cases, 'discrepancies': discrepancy,
                      'illustrative_strict_let_deletion': {
                          'binding_checker_accepts': reduced_dec_strict_purity('Error'),
                          'source_outcome': source_outcome,
                          'target_outcome': deleted_target_outcome}}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
