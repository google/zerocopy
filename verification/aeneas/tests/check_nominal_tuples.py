#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Check declaration identity and unchanged ordinary tuples in fresh extraction."""
from pathlib import Path
import re
import sys

work = Path(sys.argv[1])
nominal = (work / 'nominal/Nominal.lean').read_text()
default = (work / 'default/Nominal.lean').read_text()
# Nominal mode must retain each Rust owner as a structure, even when owners
# share fields. Default mode intentionally retains upstream tuple aliases.
for name in ('First', 'Second', 'Empty', 'OtherEmpty', 'Generic', 'OtherGeneric', 'Pair', 'OtherPair', 'Nested', 'OtherNested'):
    assert re.search(rf'^structure {name}(?:\s|$)', nominal, re.M), name
    assert re.search(rf'^def {name}(?:\s|$)', default, re.M), name
for name in ('ordinary', 'ordinary_pattern', 'ordinary_unit', 'ordinary_single'):
    pattern = rf'^def {name}\b.*?(?=\n/--|\nend NominalTuples)'
    actual = re.search(pattern, nominal, re.M | re.S)
    expected = re.search(pattern, default, re.M | re.S)
    assert actual and expected and actual.group() == expected.group(), name
print('Nominal identities and ordinary tuple compatibility checked')
