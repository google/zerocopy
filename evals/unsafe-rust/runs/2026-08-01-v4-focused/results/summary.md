# V4 Focused Confirmation Results

**Primary V4 gate: FAIL.**

Each atom cell is a pass count out of five. V4 is the confirmatory candidate; V3 is diagnostic.

| Mode | Condition | Atom pass counts | Defective reports |
|---|---|---|---:|
| P | V4 | P1 5/5; P2 5/5; P3 5/5; P4 5/5; P5 5/5; P6 5/5; P7 5/5; P8 5/5; P9 5/5; P10 5/5; P11 5/5; P12 5/5; P13 5/5; P14 5/5; P15 5/5; P16 5/5; P17 5/5; P18 5/5; P19 5/5; P20 5/5; P21 5/5; P22 5/5; P23 5/5; P24 5/5; P25 5/5; P26 5/5; P27 5/5 | 0 |
| P | V3 | P1 4/5; P2 4/5; P3 5/5; P4 5/5; P5 5/5; P6 5/5; P7 5/5; P8 5/5; P9 5/5; P10 5/5; P11 5/5; P12 4/5; P13 5/5; P14 5/5; P15 5/5; P16 5/5; P17 5/5; P18 4/5; P19 4/5; P20 4/5; P21 5/5; P22 4/5; P23 4/5; P24 4/5; P25 5/5; P26 4/5; P27 4/5 | 1 |
| B | V4 | B1 5/5; B2 2/5; B3 1/5; B4 1/5; B5 2/5; B6 2/5; B7 3/5; B8 1/5; B9 2/5; B10 1/5; B11 1/5; B12 1/5; B13 1/5; B14 1/5; B15 1/5 | 4 |
| B | V3 | B1 5/5; B2 1/5; B3 0/5; B4 0/5; B5 0/5; B6 0/5; B7 2/5; B8 0/5; B9 0/5; B10 0/5; B11 0/5; B12 0/5; B13 0/5; B14 0/5; B15 0/5 | 5 |
| L | V4 | L1 5/5; L2 5/5; L3 4/5; L4 3/5; L5 5/5; L6 3/5; L7 5/5; L8 3/5; L9 3/5; L10 2/5; L11 2/5 | 3 |
| L | V3 | L1 5/5; L2 5/5; L3 5/5; L4 5/5; L5 5/5; L6 5/5; L7 5/5; L8 5/5; L9 4/5; L10 1/5; L11 1/5 | 4 |
| Q | V4 | Q1 5/5; Q2 5/5; Q3 5/5; Q4 5/5; Q5 5/5 | 0 |
| Q | V3 | Q1 5/5; Q2 5/5; Q3 5/5; Q4 5/5; Q5 5/5 | 0 |
| R | V4 | R1 3/5; R2 3/5; R3 3/5; R4 5/5; R5 5/5; R6 5/5; R7 3/5 | 2 |
| R | V3 | R1 2/5; R2 2/5; R3 2/5; R4 5/5; R5 5/5; R6 5/5; R7 2/5 | 3 |

## Diagnostic comparison

Any V4 atom below matched V3: YES.

`TARGETED_LIFT_EVIDENCE` means V4 passed 5/5 while matched V3 was lower. `CEILING_REPLICATION` means both passed 5/5. These coherent packages differ in more than one isolated instruction, so no classification is causal proof.

| Mode | Atom | V4 | V3 | Classification |
|---|---|---:|---:|---|
| P | P1 | 5/5 | 4/5 | TARGETED_LIFT_EVIDENCE |
| P | P2 | 5/5 | 4/5 | TARGETED_LIFT_EVIDENCE |
| P | P3 | 5/5 | 5/5 | CEILING_REPLICATION |
| P | P4 | 5/5 | 5/5 | CEILING_REPLICATION |
| P | P5 | 5/5 | 5/5 | CEILING_REPLICATION |
| P | P6 | 5/5 | 5/5 | CEILING_REPLICATION |
| P | P7 | 5/5 | 5/5 | CEILING_REPLICATION |
| P | P8 | 5/5 | 5/5 | CEILING_REPLICATION |
| P | P9 | 5/5 | 5/5 | CEILING_REPLICATION |
| P | P10 | 5/5 | 5/5 | CEILING_REPLICATION |
| P | P11 | 5/5 | 5/5 | CEILING_REPLICATION |
| P | P12 | 5/5 | 4/5 | TARGETED_LIFT_EVIDENCE |
| P | P13 | 5/5 | 5/5 | CEILING_REPLICATION |
| P | P14 | 5/5 | 5/5 | CEILING_REPLICATION |
| P | P15 | 5/5 | 5/5 | CEILING_REPLICATION |
| P | P16 | 5/5 | 5/5 | CEILING_REPLICATION |
| P | P17 | 5/5 | 5/5 | CEILING_REPLICATION |
| P | P18 | 5/5 | 4/5 | TARGETED_LIFT_EVIDENCE |
| P | P19 | 5/5 | 4/5 | TARGETED_LIFT_EVIDENCE |
| P | P20 | 5/5 | 4/5 | TARGETED_LIFT_EVIDENCE |
| P | P21 | 5/5 | 5/5 | CEILING_REPLICATION |
| P | P22 | 5/5 | 4/5 | TARGETED_LIFT_EVIDENCE |
| P | P23 | 5/5 | 4/5 | TARGETED_LIFT_EVIDENCE |
| P | P24 | 5/5 | 4/5 | TARGETED_LIFT_EVIDENCE |
| P | P25 | 5/5 | 5/5 | CEILING_REPLICATION |
| P | P26 | 5/5 | 4/5 | TARGETED_LIFT_EVIDENCE |
| P | P27 | 5/5 | 4/5 | TARGETED_LIFT_EVIDENCE |
| B | B1 | 5/5 | 5/5 | CEILING_REPLICATION |
| B | B2 | 2/5 | 1/5 | V4_HIGHER_BUT_CONFIRMATION_FAILED |
| B | B3 | 1/5 | 0/5 | V4_HIGHER_BUT_CONFIRMATION_FAILED |
| B | B4 | 1/5 | 0/5 | V4_HIGHER_BUT_CONFIRMATION_FAILED |
| B | B5 | 2/5 | 0/5 | V4_HIGHER_BUT_CONFIRMATION_FAILED |
| B | B6 | 2/5 | 0/5 | V4_HIGHER_BUT_CONFIRMATION_FAILED |
| B | B7 | 3/5 | 2/5 | V4_HIGHER_BUT_CONFIRMATION_FAILED |
| B | B8 | 1/5 | 0/5 | V4_HIGHER_BUT_CONFIRMATION_FAILED |
| B | B9 | 2/5 | 0/5 | V4_HIGHER_BUT_CONFIRMATION_FAILED |
| B | B10 | 1/5 | 0/5 | V4_HIGHER_BUT_CONFIRMATION_FAILED |
| B | B11 | 1/5 | 0/5 | V4_HIGHER_BUT_CONFIRMATION_FAILED |
| B | B12 | 1/5 | 0/5 | V4_HIGHER_BUT_CONFIRMATION_FAILED |
| B | B13 | 1/5 | 0/5 | V4_HIGHER_BUT_CONFIRMATION_FAILED |
| B | B14 | 1/5 | 0/5 | V4_HIGHER_BUT_CONFIRMATION_FAILED |
| B | B15 | 1/5 | 0/5 | V4_HIGHER_BUT_CONFIRMATION_FAILED |
| L | L1 | 5/5 | 5/5 | CEILING_REPLICATION |
| L | L2 | 5/5 | 5/5 | CEILING_REPLICATION |
| L | L3 | 4/5 | 5/5 | V4_BELOW_V3 |
| L | L4 | 3/5 | 5/5 | V4_BELOW_V3 |
| L | L5 | 5/5 | 5/5 | CEILING_REPLICATION |
| L | L6 | 3/5 | 5/5 | V4_BELOW_V3 |
| L | L7 | 5/5 | 5/5 | CEILING_REPLICATION |
| L | L8 | 3/5 | 5/5 | V4_BELOW_V3 |
| L | L9 | 3/5 | 4/5 | V4_BELOW_V3 |
| L | L10 | 2/5 | 1/5 | V4_HIGHER_BUT_CONFIRMATION_FAILED |
| L | L11 | 2/5 | 1/5 | V4_HIGHER_BUT_CONFIRMATION_FAILED |
| Q | Q1 | 5/5 | 5/5 | CEILING_REPLICATION |
| Q | Q2 | 5/5 | 5/5 | CEILING_REPLICATION |
| Q | Q3 | 5/5 | 5/5 | CEILING_REPLICATION |
| Q | Q4 | 5/5 | 5/5 | CEILING_REPLICATION |
| Q | Q5 | 5/5 | 5/5 | CEILING_REPLICATION |
| R | R1 | 3/5 | 2/5 | V4_HIGHER_BUT_CONFIRMATION_FAILED |
| R | R2 | 3/5 | 2/5 | V4_HIGHER_BUT_CONFIRMATION_FAILED |
| R | R3 | 3/5 | 2/5 | V4_HIGHER_BUT_CONFIRMATION_FAILED |
| R | R4 | 5/5 | 5/5 | CEILING_REPLICATION |
| R | R5 | 5/5 | 5/5 | CEILING_REPLICATION |
| R | R6 | 5/5 | 5/5 | CEILING_REPLICATION |
| R | R7 | 3/5 | 2/5 | V4_HIGHER_BUT_CONFIRMATION_FAILED |

## Primary gates

| Gate | Result |
|---|---|
| all v4 atoms 5 of 5 | FAIL |
| zero v4 hard errors | FAIL |
| zero v4 proposal laundering | PASS |
| zero v4 tcb authority defects | FAIL |
| zero v4 semantic noncompletion | PASS |
| zero v4 scope budget defects | PASS |
| zero v4 confirmed novel findings | PASS |

## Confirmed novel findings

None.

## Integrity limitations

Filesystem and URL isolation were procedural on a shared host. Exact hosted model-build and sampling-seed metadata were unavailable. Results are source-review capability observations under those constraints.
