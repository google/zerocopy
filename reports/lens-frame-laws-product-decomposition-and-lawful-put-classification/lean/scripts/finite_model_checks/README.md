# Finite-model falsification tests (not proofs)

These scripts enumerate lenses on tiny finite types and check that statements of the package
are not refuted there. They can refute a statement; they cannot establish one. They are not
part of the Lake build.

    python3 bruteforce.py        # F1 (with Nonempty S), F1-exact, derived laws, F1-inverse, F3, F2   (~4.5 min)
    python3 bruteforce_pair.py   # pair form of F3 (ghost complement)                                 (~25 s)
    python3 count_puts.py        # counting form of F6                                                (~1 s)

`*.expected_output.txt` are the outputs of earlier runs. `bruteforce.py` tests F1 with the
hypothesis `Nonempty S`, which implies the hypothesis `Nonempty (A × B) → Nonempty S` of the
current statement; the exact (if-and-only-if) form it also tests uses the conditional condition.
F3-sharp, F3-fiber, F5 and the non-counting forms of F6 are not covered.
