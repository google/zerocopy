# Frozen Word-Count Policy

Decode `report.md` as UTF-8, split it on every Unicode whitespace run using
Python 3 `str.split()`, and count the resulting nonempty fields. Invalid UTF-8
is an invalid attempt.

The caps are:

| Mode | Maximum words |
|---|---:|
| P | 3,000 |
| B | 3,200 |
| L | 2,200 |
| Q | 1,800 |
| R | 1,800 |

The same cap applies to both conditions. A report above its cap remains
preserved but fails the source-scope/budget gate; it is not an infrastructure
failure and may not be rerun.
