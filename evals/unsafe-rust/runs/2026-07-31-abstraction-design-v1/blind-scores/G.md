# Mode G blind scores

| Report | G1 | G2 | G3 | G4 | G5 |
|---|---|---|---|---|---|
| A | PASS | PASS | PASS | PASS | FAIL |
| B | PASS | PASS | PASS | PASS | FAIL |
| C | PASS | PASS | PASS | PASS | PASS |
| D | PASS | PASS | PASS | PASS | FAIL |
| E | PASS | PASS | PASS | PASS | PASS |
| F | PASS | PASS | PASS | PASS | PASS |

## Compact notes

- **A:** G1 identifies the placeholder as no implementation and keeps its later verdict explicitly conceptual rather than current-artifact. G2 states and implements the exact rejection union and `(i, j)` return order. G3 uses only safe `split_at_mut`, assembling `(from_i[0], before_i[j])` when `j < i`, with no unsafe/helper/caller obligation. G4 proves guards, both strict-order branches, nonoverlap (including ZSTs), behavior, profiles/targets/widths, `no_std`, MSRV, and the open-range compatibility condition. G5 fails because the unimplemented conceptual design is called **PROVED** and no fresh exact-source audit after implementation is required.
- **B:** G1 explicitly gives the checked-in placeholder no verdict. G2 proves exact `None` conditions and preserves `(i, j)` in both branches. G3 prefers the direct safe split and reverses tuple assembly for `i > j`, rejecting raw pointers, unsafe helpers, and generic abstractions. G4 covers bounds, lookup success, disjoint logical intervals/lifetimes, complete behavior, ZSTs, all configurations, and the Rust-1.70+ premise. G5 fails because it certifies the proposed body **PROVED** (including conditionally over the open range) and lacks a fresh exact implemented-source audit.
- **C:** G1 says this is greenfield design, not an implementation verdict. G2 states the exact behavior and proves the original-index mapping and tuple order in both directions. G3 uses safe `split_at_mut`, reverses assembly for `j < i`, and expressly avoids unsafe code, caller obligations, and one-off generic helpers. G4 is a conditional proof plan covering rejection bounds, distinct/coexisting borrows, behavior, all `T` including ZSTs, targets/profiles, `no_std`, MSRV, and later-toolchain compatibility. G5 withholds a proof verdict from the sketch and explicitly requires re-audit after implementation of the exact snapshot.
- **D:** G1 treats the body as a placeholder and does not audit it as current implementation. G2 preserves exact rejection semantics and `(i, j)` ordering. G3 uses safe `split_at_mut`/`get_mut`, returns the upper reference first when `j < i`, and rejects unsafe/raw/helper abstractions and caller preconditions. G4 proves all bounds, two-subslice exclusivity/lifetimes, behavior, ZSTs, targets/profiles, `no_std`, Rust 1.70, and conditional later-release coverage. G5 fails because it declares the proposed body and postcondition **PROVED** before implementation and does not require a fresh exact-source post-change audit.
- **E:** G1 explicitly says no current-artifact verdict applies. G2 states and implements exactly the equal/out-of-range `None` cases and ordered successful pair. G3 selects the minimal safe split design, reverses the tuple for `j < i`, and rejects unsafe contracts, raw-pointer reasoning, caller obligations, and reusable abstractions. G4 conditionally proves every bounds/order branch, safe nonaliasing (including ZSTs), behavior, complete target/profile/no-`std` domain, MSRV, and open-ended toolchains. G5 does not give the candidate a verdict and requires inspection and proof closure against the exact implemented source.
- **F:** G1 explicitly withholds a present-artifact verdict and requires separate audit of an implemented snapshot. G2 preserves the exact rejection union and requested reference order. G3 uses only safe splitting at the larger index, reverses assembly for `j < i`, and rejects unsafe or reusable multi-borrow abstraction/caller obligations. G4 proves bounds, distinct logical partitions/lifetimes, behavior, ZSTs, all targets/profiles, `no_std`, Rust 1.70, and the explicit open-range premise. G5 calls the body a candidate and says only an exact-artifact post-implementation audit may conclude PROVED.

## Hard errors

- **A:** Certifies an unimplemented proposal as **PROVED**.
- **B:** Certifies an unimplemented proposal as **PROVED**.
- **D:** Certifies an unimplemented proposal as **PROVED**.
- **C, E, F:** No hard error identified.

No local scoring-instruction file was present directly in the mode-G bundle.
