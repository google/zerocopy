# Blind-Scoring Operational Schedule

> **Evaluator-only material.** This file contains no condition map, but keep it
> outside blind scorer packets.

Twenty fresh scorers are assigned in this randomized claim order. `s1` and
`s2` are independent replicates and must not inspect one another's output.

```text
N-s1
I-s1
A-s2
C-s1
V-s1
U-s2
C-s2
D-s2
H-s2
V-s2
P-s2
H-s1
N-s2
T-s2
D-s1
U-s1
P-s1
I-s2
A-s1
T-s1
```

Scorers receive only their mode packet and unique empty output directory. A
claim directory under the scoring runtime is the sole ownership record.
