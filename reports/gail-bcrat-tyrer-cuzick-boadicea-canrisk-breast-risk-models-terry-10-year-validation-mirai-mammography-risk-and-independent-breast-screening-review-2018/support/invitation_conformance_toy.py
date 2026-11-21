#!/usr/bin/env python3
"""Specification-conformance probe for screening-invitation cohort rules.

TOY MODEL. This encodes, in a few lines, the eligibility rules *as described in
prose* by the Independent Breast Screening Review 2018 (HC 1799, paras 2.5-2.9,
2.16-2.18, 2.25, 1.25). It is not the code of any national screening system and
its counts are properties of the synthetic grid below, not of any programme.

Rules compared (all ages in completed years):
  SPEC_71   - invite while age at the screening date is < 71
              ("until they reach the age of 71", November 2013 specification text).
  YOB_70    - include a woman in a batch if (batch screening year - birth year)
              lies in [50, 70] ("calendar age", year in which she turns N).
  AGEX_SEL  - YOB_70, but the upper bound is computed from the *batch selection
              date* entered by staff: min_birth_year = selection_year - 70; a woman
              born before min_birth_year receives AgeX code 2 and is excluded when
              the batch is randomised to the lower-extension arm (para 2.25).
The probe reports, over a grid of birth dates x batch dates x selection-date
offsets, how often each rule pair disagrees, and prints the Review's own
worked example as a regression case.
"""
from datetime import date, timedelta
from itertools import product

def age_on(born, d):
    return d.year - born.year - ((d.month, d.day) < (born.month, born.day))

def spec_71(born, screen):
    return 50 <= age_on(born, screen) < 71

def yob_70(born, screen):
    return 50 <= screen.year - born.year <= 70

def agex_sel(born, screen, selection, lower_arm=True):
    if not (47 <= screen.year - born.year <= 73):
        return False
    min_yob = selection.year - 70
    code2 = born.year < min_yob
    code1 = screen.year - born.year < 50
    if code2 and lower_arm:
        return False
    if code1 and not lower_arm:
        return False
    return not code1  # count only core-range women for the comparison

# The Review's worked example (para 2.25).
born = date(1945, 12, 15)
screen = date(2015, 12, 1)
for sel in (date(2015, 11, 1), date(2016, 1, 4)):
    print(f'example born={born} screen={screen} selection={sel}: age={age_on(born, screen)} '
          f'SPEC_71={spec_71(born, screen)} YOB_70={yob_70(born, screen)} '
          f'AGEX_SEL(lower arm)={agex_sel(born, screen, sel)}')

# Grid: birth dates every 7 days over 1940-1950; screening dates on the 1st of
# each month 2014-2017; selection date = screening date + offset days.
births = [date(1940, 1, 3) + timedelta(days=7 * k) for k in range(0, 52 * 11)]
screens = [date(y, m, 1) for y in range(2014, 2018) for m in range(1, 13)]
offsets = [-45, 0, 45]
pairs = {('SPEC_71', 'YOB_70'): [0, 0], ('YOB_70', 'AGEX_SEL'): [0, 0], ('SPEC_71', 'AGEX_SEL'): [0, 0]}
ages_spec_not_yob = {}
n = 0
for b, s, off in product(births, screens, offsets):
    sel = s + timedelta(days=off)
    r = {'SPEC_71': spec_71(b, s), 'YOB_70': yob_70(b, s), 'AGEX_SEL': agex_sel(b, s, sel)}
    n += 1
    for (x, y), c in pairs.items():
        if r[x] and not r[y]:
            c[0] += 1
        if r[y] and not r[x]:
            c[1] += 1
    if r['SPEC_71'] and not r['YOB_70']:
        a = age_on(b, s)
        ages_spec_not_yob[a] = ages_spec_not_yob.get(a, 0) + 1
print(f'grid cases: {n} (births={len(births)} screens={len(screens)} offsets={offsets})')
for (x, y), (xy, yx) in pairs.items():
    print(f'{x} true & {y} false: {xy:6d}   {y} true & {x} false: {yx:6d}')
print('ages (at screening) where SPEC_71 includes but YOB_70 excludes:', dict(sorted(ages_spec_not_yob.items())))
