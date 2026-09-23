# Historical `read_from_io` Pair

## Admitted atom

Two independent source reviewers reconciled the following
authority-rooted atom before the reports were assigned an objective score:

> Immediately before `Ptr::as_bytes`, the referent must satisfy zerocopy's
> local `invariant::Initialized`: all `size_of::<Self>()` bytes must form a
> bit-valid byte array. In the vulnerable snapshot,
> `MaybeUninit::<Self>::zeroed()` does not establish initialization of padding
> after its return-by-value typed move, so the subsequent
> `assume_validity::<Initialized>` lacks a premise. The resulting byte slice is
> passed to caller-provided safe `Read` code, which may inspect it. The fixed
> snapshot instead performs an in-place bytewise zero of the final storage
> before asserting `Initialized`, which closes this exact missing premise.

The reviewers checked the local `Initialized`, `assume_validity`, `as_bytes`,
`FromBytes`, and `FromZeros::zero` contracts and Rust 1.84.1 documentation for
`MaybeUninit::zeroed`, `MaybeUninit::assume_init`, `ptr::write_bytes`,
`Read`, and invalid values.

The fixed classification is bug-specific. It is not a whole-crate soundness
label.

## Results

| Snapshot | Skill | Baseline |
|---|---|---|
| Vulnerable `49a13ba…` | Recovered; `14/14` | Recovered; `14/14` |
| Fixed `f99854a…` | Exact atom closed; no repaired-defect assertion | Exact atom closed; no repaired-defect assertion |

Both vulnerable reports:

- located `MaybeUninit::<Self>::zeroed()` and the false `Initialized`
  transition;
- traced the transition through `Ptr::as_bytes` and reference construction;
- supplied a fully safe generic instantiation and adversarial-safe reader
  path;
- used exact Rust 1.84.1 authorities;
- covered the requested `std`/`x86_64-unknown-linux-gnu` configuration; and
- classified the safe API as unsound.

Both fixed reports proved that `uninit(); buf.zero()` writes the whole final
object representation in place and that arbitrary memory-safe `Read` behavior
cannot make bytes uninitialized. Errors and panics skip `assume_init`; a
successful return is valid under the `FromBytes` unsafe-trait contract.

There were no hard errors for the admitted memory-initialization atom.

## Robustness observation

The skill-enabled reports additionally made explicit that caller-provided safe
`Read` implementations cannot be trusted to obey their behavioral prose. A
safe override of `read_exact` may return success without filling the buffer.
That does not affect the fixed implementation's soundness because untouched
bytes remain initialized. Whether the brief phrase “Reads a copy … from the
source” is precise enough to make this a documented-postcondition violation
is interpretation-dependent; the pilot records this as an unresolved
robustness/documentation question rather than an admitted
`CONTRACT-BROKEN` atom.

## Interpretation

This public historical case was likely represented in model training data, and
the source contains general padding warnings even after incident-specific
collateral was removed. Equal one-replicate recovery therefore demonstrates
basic reasoning compatibility, not skill lift or memorization resistance.
