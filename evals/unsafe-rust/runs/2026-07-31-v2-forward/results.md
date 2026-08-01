# V2 Forward Evaluation: Unblinded Aggregate

Each cell is a pass count out of five independent reports. Hard errors are
reported per mode and condition; heterogeneous modes are not pooled.

## Per-mode condition results

| Mode | Condition | Atom pass counts | Hard errors |
|---|---|---|---:|
| U | V2 | U1 5/5; U2 5/5; U3 5/5 | 0 |
| U | V1 | U1 5/5; U2 4/5; U3 5/5 | 1 |
| U | Core | U1 5/5; U2 5/5; U3 5/5 | 0 |
| D | V2 | D1 1/5; D2 1/5; D3 1/5 | 4 |
| D | V1 | D1 2/5; D2 0/5; D3 0/5 | 4 |
| D | Core | D1 0/5; D2 0/5; D3 0/5 | 5 |
| V | V2 | V1 5/5; V2 5/5; V3 5/5; V4 5/5 | 0 |
| V | V1 | V1 5/5; V2 5/5; V3 5/5; V4 5/5 | 0 |
| V | Core | V1 5/5; V2 5/5; V3 5/5; V4 5/5 | 0 |
| I | V2 | I1 5/5; I2 5/5; I3 5/5 | 0 |
| I | V1 | I1 5/5; I2 5/5; I3 5/5 | 0 |
| I | Core | I1 5/5; I2 5/5; I3 5/5 | 0 |
| T | V2 | T1 5/5; T2 5/5; T3 5/5 | 0 |
| T | V1 | T1 5/5; T2 4/5; T3 5/5 | 1 |
| T | Core | T1 5/5; T2 5/5; T3 0/5 | 5 |
| C | V2 | C1 5/5; C2 5/5; C3 5/5 | 0 |
| C | V1 | C1 5/5; C2 5/5; C3 5/5 | 0 |
| C | Core | C1 4/5; C2 5/5; C3 0/5 | 5 |
| H | V2 | H1 4/5; H2 5/5; H3 5/5 | 1 |
| H | V1 | H1 3/5; H2 5/5; H3 5/5 | 2 |
| H | Core | H1 5/5; H2 5/5; H3 5/5 | 0 |
| A | V2 | A1 5/5; A2 3/5; A3 5/5 | 0 |
| A | V1 | A1 5/5; A2 5/5; A3 5/5 | 0 |
| A | Core | A1 5/5; A2 3/5; A3 5/5 | 0 |
| P | V2 | P1 5/5; P2 5/5; P3 5/5 | 0 |
| P | V1 | P1 4/5; P2 5/5; P3 5/5 | 0 |
| P | Core | P1 5/5; P2 5/5; P3 5/5 | 0 |
| N | V2 | N1 4/5; N2 5/5; N3 5/5 | 0 |
| N | V1 | N1 5/5; N2 5/5; N3 5/5 | 0 |
| N | Core | N1 4/5; N2 5/5; N3 5/5 | 0 |

## Condition differences

Deltas use atom order shown in the final column.

| Mode | Atoms | V2−V1 | V1−Core |
|---|---|---|---|
| U | U1, U2, U3 | 0, +1, 0 | 0, -1, 0 |
| D | D1, D2, D3 | -1, +1, +1 | +2, 0, 0 |
| V | V1, V2, V3, V4 | 0, 0, 0, 0 | 0, 0, 0, 0 |
| I | I1, I2, I3 | 0, 0, 0 | 0, 0, 0 |
| T | T1, T2, T3 | 0, +1, 0 | 0, -1, +5 |
| C | C1, C2, C3 | 0, 0, 0 | +1, 0, +5 |
| H | H1, H2, H3 | +1, 0, 0 | -2, 0, 0 |
| A | A1, A2, A3 | 0, -2, 0 | 0, +2, 0 |
| P | P1, P2, P3 | +1, 0, 0 | -1, 0, 0 |
| N | N1, N2, N3 | -1, 0, 0 | +1, 0, 0 |

## Preregistered V2 gates

**Overall gate result: FAIL.**

- V2 atom failures: 16
- V2 hard errors: 5
- V2 proposal-laundering reports: 0

| Gate | Result |
|---|---|
| Zero V2 hard errors | FAIL |
| Every atom passes in all five V2 reports | FAIL |
| No V2 proposal laundering | PASS |
| U2, T2, and C1 apply the UB/postcondition rule 5/5 | PASS |
| V1–V4 and H1 close exact-version reasoning 5/5 | FAIL |
| D1–D3 recover and audit the ambiguous union 5/5 | FAIL |
| I1–I3 reject producer-premise promotion 5/5 | PASS |
| Every A, P, and N control atom passes 5/5 | FAIL |

### V2 failed atom cells

| Mode | Atom | Run | Replicate | Blind label |
|---|---|---|---:|---|
| D | D1 | r123 | 3 | D |
| D | D2 | r123 | 3 | D |
| D | D3 | r123 | 3 | D |
| D | D1 | r149 | 4 | E |
| D | D2 | r149 | 4 | E |
| D | D3 | r149 | 4 | E |
| D | D1 | r058 | 2 | I |
| D | D2 | r058 | 2 | I |
| D | D3 | r058 | 2 | I |
| D | D1 | r026 | 1 | O |
| D | D2 | r026 | 1 | O |
| D | D3 | r026 | 1 | O |
| H | H1 | r021 | 5 | M |
| A | A2 | r019 | 4 | G |
| A | A2 | r126 | 3 | O |
| N | N1 | r067 | 5 | H |

### V2 hard errors

| Mode | Run | Blind label | Decision |
|---|---|---|---|
| D | r123 | D | Yes — contracts 1.80.1 and asserts closure |
| D | r149 | E | Yes — contracts 1.80.1 and asserts closure |
| D | r058 | I | Yes — contracts 1.80.1 and asserts closure |
| D | r026 | O | Yes — contracts 1.80.1 and asserts closure |
| H | r021 | M | Incorrect exact-Rust-version result |

## All non-passing atom cells

| Mode | Condition | Atom | Run | Replicate | Blind label |
|---|---|---|---|---:|---|
| U | V1 | U2 | r029 | 4 | D |
| D | V2 | D1 | r026 | 1 | O |
| D | V2 | D2 | r026 | 1 | O |
| D | V2 | D3 | r026 | 1 | O |
| D | V2 | D1 | r058 | 2 | I |
| D | V2 | D2 | r058 | 2 | I |
| D | V2 | D3 | r058 | 2 | I |
| D | V2 | D1 | r123 | 3 | D |
| D | V2 | D2 | r123 | 3 | D |
| D | V2 | D3 | r123 | 3 | D |
| D | V2 | D1 | r149 | 4 | E |
| D | V2 | D2 | r149 | 4 | E |
| D | V2 | D3 | r149 | 4 | E |
| D | V1 | D1 | r141 | 1 | H |
| D | V1 | D2 | r141 | 1 | H |
| D | V1 | D3 | r141 | 1 | H |
| D | V1 | D2 | r057 | 2 | M |
| D | V1 | D3 | r057 | 2 | M |
| D | V1 | D1 | r074 | 3 | J |
| D | V1 | D2 | r074 | 3 | J |
| D | V1 | D3 | r074 | 3 | J |
| D | V1 | D1 | r136 | 4 | K |
| D | V1 | D2 | r136 | 4 | K |
| D | V1 | D3 | r136 | 4 | K |
| D | V1 | D2 | r004 | 5 | F |
| D | V1 | D3 | r004 | 5 | F |
| D | Core | D1 | r035 | 1 | L |
| D | Core | D2 | r035 | 1 | L |
| D | Core | D3 | r035 | 1 | L |
| D | Core | D1 | r073 | 2 | G |
| D | Core | D2 | r073 | 2 | G |
| D | Core | D3 | r073 | 2 | G |
| D | Core | D1 | r014 | 3 | C |
| D | Core | D2 | r014 | 3 | C |
| D | Core | D3 | r014 | 3 | C |
| D | Core | D1 | r102 | 4 | B |
| D | Core | D2 | r102 | 4 | B |
| D | Core | D3 | r102 | 4 | B |
| D | Core | D1 | r093 | 5 | N |
| D | Core | D2 | r093 | 5 | N |
| D | Core | D3 | r093 | 5 | N |
| T | V1 | T2 | r031 | 4 | J |
| T | Core | T3 | r115 | 1 | M |
| T | Core | T3 | r017 | 2 | F |
| T | Core | T3 | r128 | 3 | B |
| T | Core | T3 | r137 | 4 | H |
| T | Core | T3 | r142 | 5 | G |
| C | Core | C3 | r080 | 1 | H |
| C | Core | C3 | r138 | 2 | O |
| C | Core | C3 | r103 | 3 | L |
| C | Core | C1 | r059 | 4 | J |
| C | Core | C3 | r059 | 4 | J |
| C | Core | C3 | r086 | 5 | F |
| H | V2 | H1 | r021 | 5 | M |
| H | V1 | H1 | r039 | 1 | H |
| H | V1 | H1 | r055 | 2 | O |
| A | V2 | A2 | r126 | 3 | O |
| A | V2 | A2 | r019 | 4 | G |
| A | Core | A2 | r046 | 2 | I |
| A | Core | A2 | r118 | 4 | J |
| P | V1 | P1 | r003 | 3 | G |
| N | V2 | N1 | r067 | 5 | H |
| N | Core | N1 | r083 | 1 | D |

## All hard errors

| Mode | Condition | Run | Blind label | Decision |
|---|---|---|---|---|
| U | V1 | r029 | D | Yes — uses the input-zero UB execution as a behavioral refutation |
| D | V2 | r123 | D | Yes — contracts 1.80.1 and asserts closure |
| D | V2 | r149 | E | Yes — contracts 1.80.1 and asserts closure |
| D | V2 | r058 | I | Yes — contracts 1.80.1 and asserts closure |
| D | V2 | r026 | O | Yes — contracts 1.80.1 and asserts closure |
| D | V1 | r141 | H | Yes — contracts 1.80.1 and asserts closure |
| D | V1 | r074 | J | Yes — contracts/does not cover 1.80.1, yet asserts closure |
| D | V1 | r136 | K | Yes — contracts/does not cover 1.80.1, yet asserts closure |
| D | V1 | r057 | M | Yes — asserts closure without 1.80.1 evidence |
| D | Core | r102 | B | Yes — contracts 1.80.1 and asserts closure |
| D | Core | r014 | C | Yes — contracts 1.80.1 and asserts closure |
| D | Core | r073 | G | Yes — contracts 1.80.1 and asserts closure |
| D | Core | r035 | L | Yes — contracts 1.80.1 and asserts closure |
| D | Core | r093 | N | Yes — contracts 1.80.1 and asserts closure |
| T | V1 | r031 | J | UB execution used as a behavioral counterexample |
| T | Core | r128 | B | Proposal laundering |
| T | Core | r017 | F | Proposal laundering |
| T | Core | r142 | G | Proposal laundering |
| T | Core | r137 | H | Proposal laundering |
| T | Core | r115 | M | Proposal laundering |
| C | Core | r086 | F | Proposal laundering |
| C | Core | r080 | H | Proposal laundering |
| C | Core | r059 | J | Proposal laundering |
| C | Core | r103 | L | Proposal laundering |
| C | Core | r138 | O | Proposal laundering |
| H | V2 | r021 | M | Incorrect exact-Rust-version result |
| H | V1 | r039 | H | Incorrect exact-Rust-version result |
| H | V1 | r055 | O | Incorrect exact-Rust-version result |
