#!/usr/bin/env python3
"""Finite outcome witnesses for relation strength. No compiler is executed."""
import json

OK = ("ok", 1)
FAIL = ("fail", None)
DIV = ("div", None)


def successes(outcomes):
    return {outcome for outcome in outcomes if outcome[0] == "ok"}


def success_inclusion(source, model, represented):
    # Deliberately weak: successful source outputs only.
    return all(successes(source[x]) <= successes(model[x]) for x in represented)


def reflects_failure(source, model, represented):
    return all(FAIL not in source[x] or FAIL in model[x] for x in represented)


def partial_true(outcomes):
    return all(outcome[0] in {"ok", "div"} for outcome in outcomes)


def examine(source, model, represented, permitted):
    return {"successful_result_inclusion": success_inclusion(source, model, represented),
            "failure_exposure_on_represented_entries": reflects_failure(source, model, represented),
            "entry_coverage": set(permitted) <= set(represented),
            "all_represented_model_partial_true": all(partial_true(model[x]) for x in represented),
            "bad_source_inputs": [x for x in permitted if FAIL in source[x]]}


def main():
    permitted = [0, 1, 2]
    guarded = {0: {OK}, 1: {OK}, 2: {FAIL}}
    erased = {x: {OK} for x in permitted}
    diverging = {0: {OK}, 1: {OK}, 2: {DIV}}
    nondeterministic = {0: {OK}, 1: {OK}, 2: {OK, FAIL}}
    results = {
        "guard_removed": examine(guarded, erased, permitted, permitted),
        "bad_replaced_by_divergence": examine(guarded, diverging, permitted, permitted),
        "bad_nondeterministic_choice_removed": examine(nondeterministic, erased, permitted, permitted),
        "entry_domain_narrowed": examine(guarded, erased, [0, 1], permitted),
    }
    for name, result in results.items():
        assert result["successful_result_inclusion"], name
        assert result["all_represented_model_partial_true"], name
        assert not (result["failure_exposure_on_represented_entries"] and result["entry_coverage"]), name
    assert results["entry_domain_narrowed"]["failure_exposure_on_represented_entries"]
    assert not results["entry_domain_narrowed"]["entry_coverage"]
    # Positive control: retain the bad branch. Its partial contract cannot hold.
    positive = examine(guarded, guarded, permitted, permitted)
    assert positive["failure_exposure_on_represented_entries"] and positive["entry_coverage"]
    assert not positive["all_represented_model_partial_true"]
    results["positive_control_retained_failure"] = positive
    print(json.dumps({"scope": "three entry states and finite explicit outcome sets",
                      "cases": results}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
