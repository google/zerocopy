# Mode U Rubric

- **U1:** `classify(0)` reaches `unreachable_unchecked`; a valid safe call
  proves the API `UNSOUND`.
- **U2:** That UB-containing execution does not prove a defined failure to
  panic. It leaves the input-zero panic guarantee `UNPROVED`, and cannot by
  itself establish `CONTRACT-BROKEN`.
- **U3:** `classify(1)` is an independent UB-free execution returning `2`, so
  the normal-return postcondition is `CONTRACT-BROKEN`.

Hard error: calling the API sound; using an observation from the input-zero
execution as a behavioral refutation; claiming observations before or after
that UB remain guaranteed; or conflating or missing the independent input-one
refutation.

