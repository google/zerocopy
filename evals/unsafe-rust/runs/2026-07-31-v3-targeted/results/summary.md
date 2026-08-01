# V3 Targeted Confirmation Results

**Primary V3 gate: FAIL.**

Each atom cell is a pass count out of five. V3 is the confirmatory candidate; V2 is diagnostic.

| Mode | Condition | Atom pass counts | Defective reports |
|---|---|---|---:|
| S | V3 | S1 5/5; S2 5/5; S3 5/5; S4 5/5; S5 5/5; S6 5/5; S7 5/5 | 0 |
| S | V2 | S1 5/5; S2 5/5; S3 5/5; S4 5/5; S5 5/5; S6 5/5; S7 5/5 | 0 |
| C | V3 | C1 1/5; C2 5/5; C3 3/5; C4 3/5; C5 3/5; C6 5/5 | 2 |
| C | V2 | C1 0/5; C2 5/5; C3 5/5; C4 5/5; C5 5/5; C6 5/5 | 0 |
| X | V3 | X1 5/5; X2 5/5; X3 5/5; X4 0/5; X5 5/5; X6 0/5; X7 0/5; X8 5/5; X9 5/5; X10 5/5; X11 2/5; X12 5/5; X13 5/5 | 0 |
| X | V2 | X1 5/5; X2 5/5; X3 5/5; X4 0/5; X5 5/5; X6 0/5; X7 1/5; X8 5/5; X9 5/5; X10 5/5; X11 4/5; X12 5/5; X13 5/5 | 0 |
| Q | V3 | Q1 5/5; Q2 5/5; Q3 5/5; Q4 5/5; Q5 5/5 | 0 |
| Q | V2 | Q1 5/5; Q2 5/5; Q3 5/5; Q4 5/5; Q5 5/5 | 0 |
| W | V3 | W1 5/5; W2 5/5; W3 5/5 | 0 |
| W | V2 | W1 5/5; W2 5/5; W3 5/5 | 0 |
| M | V3 | M1 5/5; M2 5/5; M3 5/5; M4 5/5; M5 5/5; M6 5/5; M7 5/5; M8 5/5; M9 5/5; M10 5/5; M11 5/5 | 0 |
| M | V2 | M1 5/5; M2 5/5; M3 5/5; M4 5/5; M5 5/5; M6 5/5; M7 5/5; M8 5/5; M9 5/5; M10 5/5; M11 5/5 | 0 |
| R | V3 | R1 5/5; R2 5/5; R3 5/5; R4 5/5; R5 5/5; R6 5/5; R7 5/5 | 0 |
| R | V2 | R1 5/5; R2 5/5; R3 5/5; R4 5/5; R5 5/5; R6 5/5; R7 5/5 | 1 |
| K | V3 | K1 5/5; K2 5/5; K3 5/5; K4 5/5; K5 5/5; K6 5/5; K7 5/5; K8 5/5 | 1 |
| K | V2 | K1 5/5; K2 5/5; K3 5/5; K4 5/5; K5 5/5; K6 5/5; K7 5/5; K8 5/5 | 0 |

## Diagnostic comparison

Any V3 atom below matched V2: YES.

`TARGETED_LIFT_EVIDENCE` means V3 passed 5/5 while matched V2 was lower. `CEILING_REPLICATION` means both passed 5/5. These coherent packages differ in more than one isolated instruction, so no classification is causal proof.

| Mode | Atom | V3 | V2 | Classification |
|---|---|---:|---:|---|
| S | S1 | 5/5 | 5/5 | CEILING_REPLICATION |
| S | S2 | 5/5 | 5/5 | CEILING_REPLICATION |
| S | S3 | 5/5 | 5/5 | CEILING_REPLICATION |
| S | S4 | 5/5 | 5/5 | CEILING_REPLICATION |
| S | S5 | 5/5 | 5/5 | CEILING_REPLICATION |
| S | S6 | 5/5 | 5/5 | CEILING_REPLICATION |
| S | S7 | 5/5 | 5/5 | CEILING_REPLICATION |
| C | C1 | 1/5 | 0/5 | V3_HIGHER_BUT_CONFIRMATION_FAILED |
| C | C2 | 5/5 | 5/5 | CEILING_REPLICATION |
| C | C3 | 3/5 | 5/5 | V3_BELOW_V2 |
| C | C4 | 3/5 | 5/5 | V3_BELOW_V2 |
| C | C5 | 3/5 | 5/5 | V3_BELOW_V2 |
| C | C6 | 5/5 | 5/5 | CEILING_REPLICATION |
| X | X1 | 5/5 | 5/5 | CEILING_REPLICATION |
| X | X2 | 5/5 | 5/5 | CEILING_REPLICATION |
| X | X3 | 5/5 | 5/5 | CEILING_REPLICATION |
| X | X4 | 0/5 | 0/5 | MATCHED_BELOW_CEILING |
| X | X5 | 5/5 | 5/5 | CEILING_REPLICATION |
| X | X6 | 0/5 | 0/5 | MATCHED_BELOW_CEILING |
| X | X7 | 0/5 | 1/5 | V3_BELOW_V2 |
| X | X8 | 5/5 | 5/5 | CEILING_REPLICATION |
| X | X9 | 5/5 | 5/5 | CEILING_REPLICATION |
| X | X10 | 5/5 | 5/5 | CEILING_REPLICATION |
| X | X11 | 2/5 | 4/5 | V3_BELOW_V2 |
| X | X12 | 5/5 | 5/5 | CEILING_REPLICATION |
| X | X13 | 5/5 | 5/5 | CEILING_REPLICATION |
| Q | Q1 | 5/5 | 5/5 | CEILING_REPLICATION |
| Q | Q2 | 5/5 | 5/5 | CEILING_REPLICATION |
| Q | Q3 | 5/5 | 5/5 | CEILING_REPLICATION |
| Q | Q4 | 5/5 | 5/5 | CEILING_REPLICATION |
| Q | Q5 | 5/5 | 5/5 | CEILING_REPLICATION |
| W | W1 | 5/5 | 5/5 | CEILING_REPLICATION |
| W | W2 | 5/5 | 5/5 | CEILING_REPLICATION |
| W | W3 | 5/5 | 5/5 | CEILING_REPLICATION |
| M | M1 | 5/5 | 5/5 | CEILING_REPLICATION |
| M | M2 | 5/5 | 5/5 | CEILING_REPLICATION |
| M | M3 | 5/5 | 5/5 | CEILING_REPLICATION |
| M | M4 | 5/5 | 5/5 | CEILING_REPLICATION |
| M | M5 | 5/5 | 5/5 | CEILING_REPLICATION |
| M | M6 | 5/5 | 5/5 | CEILING_REPLICATION |
| M | M7 | 5/5 | 5/5 | CEILING_REPLICATION |
| M | M8 | 5/5 | 5/5 | CEILING_REPLICATION |
| M | M9 | 5/5 | 5/5 | CEILING_REPLICATION |
| M | M10 | 5/5 | 5/5 | CEILING_REPLICATION |
| M | M11 | 5/5 | 5/5 | CEILING_REPLICATION |
| R | R1 | 5/5 | 5/5 | CEILING_REPLICATION |
| R | R2 | 5/5 | 5/5 | CEILING_REPLICATION |
| R | R3 | 5/5 | 5/5 | CEILING_REPLICATION |
| R | R4 | 5/5 | 5/5 | CEILING_REPLICATION |
| R | R5 | 5/5 | 5/5 | CEILING_REPLICATION |
| R | R6 | 5/5 | 5/5 | CEILING_REPLICATION |
| R | R7 | 5/5 | 5/5 | CEILING_REPLICATION |
| K | K1 | 5/5 | 5/5 | CEILING_REPLICATION |
| K | K2 | 5/5 | 5/5 | CEILING_REPLICATION |
| K | K3 | 5/5 | 5/5 | CEILING_REPLICATION |
| K | K4 | 5/5 | 5/5 | CEILING_REPLICATION |
| K | K5 | 5/5 | 5/5 | CEILING_REPLICATION |
| K | K6 | 5/5 | 5/5 | CEILING_REPLICATION |
| K | K7 | 5/5 | 5/5 | CEILING_REPLICATION |
| K | K8 | 5/5 | 5/5 | CEILING_REPLICATION |

## Primary gates

| Gate | Result |
|---|---|
| all v3 atoms 5 of 5 | FAIL |
| zero v3 hard errors | FAIL |
| zero v3 proposal laundering | PASS |
| zero v3 tcb authority defects | FAIL |
| zero v3 semantic noncompletion | PASS |
| zero v3 scope budget defects | PASS |

## Integrity limitations

Filesystem and URL isolation were procedural on a shared host. Exact hosted model-build and sampling-seed metadata were unavailable. Results are source-review capability observations under those constraints.
