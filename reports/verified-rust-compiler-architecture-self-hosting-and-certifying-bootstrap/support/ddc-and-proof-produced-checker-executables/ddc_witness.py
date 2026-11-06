#!/usr/bin/env python3
"""Original finite DDC illustration; no real compiler/proof replay."""
import json
import sys

sys.dont_write_bytecode = True
CLEAN = b'clean-compiler-executable'
INFECTED = b'infected-compiler-executable'
CLEAN_SOURCE = b'compiler source: implement clean compilation'
BAD_SOURCE = b'compiler source: implement persistent infection'
APP_SOURCE = b'checker source: accept exactly when input equals expected'


def compile_source(compiler, source):
    assert compiler in (CLEAN, INFECTED)
    if source == CLEAN_SOURCE:
        return INFECTED if compiler == INFECTED else CLEAN
    if source == BAD_SOURCE:
        return INFECTED
    if source == APP_SOURCE:
        return b'accept-all' if compiler == INFECTED else b'check-equality'
    raise ValueError('outside finite source domain')


def ddc(candidate_source):
    # Trusted diverse compiler accurately builds either declared compiler source.
    stage1 = compile_source(CLEAN, candidate_source)
    stage2 = compile_source(stage1, candidate_source)
    return stage1, stage2


def run_checker(executable, value, expected):
    if executable == b'accept-all':
        return True
    assert executable == b'check-equality'
    return value == expected


def main():
    regenerated = compile_source(INFECTED, CLEAN_SOURCE)
    assert regenerated == INFECTED
    stage1, stage2 = ddc(CLEAN_SOURCE)
    assert stage1 == CLEAN and stage2 == CLEAN and stage2 != INFECTED
    bad_stage1, bad_stage2 = ddc(BAD_SOURCE)
    assert bad_stage1 == INFECTED and bad_stage2 == INFECTED
    actual_checker = compile_source(bad_stage2, APP_SOURCE)
    actual = run_checker(actual_checker, 1, 2)
    intended = 1 == 2
    assert actual is True and intended is False
    print(json.dumps({
        'scope': 'original finite illustration, no actual DDC/compiler experiment',
        'hidden_infection_passes_regeneration': True,
        'diverse_second_stage_detects_hidden_infection': True,
        'deliberately_bad_compiler_source_passes_ddc': True,
        'source_correspondence_does_not_imply_application_checker_soundness': True,
        'bad_compiler_result': actual,
        'independent_intended_result': intended,
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
