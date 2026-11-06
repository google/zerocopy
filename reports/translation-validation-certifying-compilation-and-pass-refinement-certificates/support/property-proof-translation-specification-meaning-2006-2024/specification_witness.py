#!/usr/bin/env python3
"""Finite property/meaning separations. No PotPie or proof assistant runs."""
import json


def truth_agreement(left, right, domain):
    return all(left(x) == right(x) for x in domain)


def main():
    domain = [0, 1, 2]
    source = {'x': 0, 'y': 10}
    target = {'x': 0, 'y': 11}
    selected = lambda state: state['x'] == 0
    partial_property = {'source_satisfies': selected(source),
                        'target_satisfies': selected(target),
                        'full_states_equal': source == target}
    original_post = lambda x: x == 1
    generated_post = lambda x: True
    correlated = {'source_output': 1, 'target_output': 2,
                  'source_satisfies_original': original_post(1),
                  'target_satisfies_generated': generated_post(2),
                  'target_satisfies_original': original_post(2),
                  'independent_spec_meaning_agreement': truth_agreement(original_post, generated_post, domain)}
    original_pre = lambda x: True
    generated_pre = lambda x: False
    vacuous = {'target_hoare_condition_holds': all(not generated_pre(x) or original_post(2) for x in domain),
               'independent_entry_meaning_agreement': truth_agreement(original_pre, generated_pre, domain)}
    assert partial_property == {'source_satisfies': True, 'target_satisfies': True,
                                'full_states_equal': False}
    assert correlated['source_satisfies_original'] and correlated['target_satisfies_generated']
    assert not correlated['target_satisfies_original']
    assert not correlated['independent_spec_meaning_agreement']
    assert vacuous['target_hoare_condition_holds']
    assert not vacuous['independent_entry_meaning_agreement']
    print(json.dumps({'scope': 'complete truth checks on x in {0,1,2} for defined predicates',
                      'selected_property': partial_property,
                      'correlated_specification_weakening': correlated,
                      'vacuous_precondition': vacuous}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
