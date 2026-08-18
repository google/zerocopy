# V5 Diagnostic Oracle — V: Valid Use and Obligation Ownership

> **DRAFT / evaluator-only.** Never expose this key, its atom graph, verdicts,
> defect rules, or authority packet to a report agent.

## Scoring contract

Use `../atoms/V.json` for direct proposition decisions and
`../rules/defect-rules.json` for the closed defect IDs. Accept an equivalent
derivation. Do not infer a failed atom from a prerequisite and do not turn a
mere omission into a hard error.

## Exact domains

There are two different obligation domains:

1. For the shipped library, the crate owns the truth of its `unsafe impl Slot
   for Anchor`; ordinary safe callers of `choose::<Anchor>` and `owned` do not.
2. For a downstream `unsafe impl Slot for Local`, the downstream implementer
   owns the unsafe-trait assertion. A proposed caller example is valid only if
   that unsafe act satisfies `index() < 2`.

The compiler requiring `unsafe impl` is not proof that the assertion is true.
Conversely, an unsafe block or unsafe-impl token does not make a false caller
contract true.

## Exact results

### Shipped `Anchor`, `choose`, and `owned`

`Anchor::index()` returns contextually typed `usize` value 2 although the
crate's unsafe-trait contract requires every result below 2. The crate-owned
unsafe impl is false and remains inside the audited library scope.

A downstream caller may safely form, for example:

```rust
let _ = valid_use_target::owned(&[11, 29]);
// equivalently for the generic surface:
let _ = valid_use_target::choose::<valid_use_target::Anchor>(&[11, 29]);
```

These ordinary safe calls require no caller unsafe act. Execution reaches
`get_unchecked(2)` on a two-element array; index 2 is out of bounds and the
Rust 1.83 contract makes the call UB. Therefore `owned` is **UNSOUND**, and
the shipped public `choose` surface is also **UNSOUND** because its valid safe
instantiation with the crate's own `Anchor` closes the same certificate.

This does not negate the conditional local consumer theorem: if a `Slot`
implementation truly satisfies the unsafe-trait postcondition, `choose`'s
local `get_unchecked` obligation is discharged.

### Downstream `East`

The public trait is accessible and the caller-local type satisfies the orphan
rule. The unsuffixed `2` is inferred as `usize`. But `unsafe impl Slot for
East` asserts `index() < 2` while returning 2. That unsafe act violates its
documented implementer contract. `example_east` is therefore **not a valid-use
refutation** of the generic consumer. The ordinary `choose` call being safe
syntax does not repair the invalid unsafe impl which made the type eligible.

### Downstream `West`

`West` is likewise accessible/coherent, but returns contextually typed index
1 and satisfies the unsafe-trait contract. `example_west` is a valid caller;
the length-2 `get_unchecked(1)` obligation is true and the result is 29. This
is a **PROVED valid control** for the conditional generic-consumer theorem.

## Authority and separation

The proof consumes public visibility, downstream-local trait implementation,
contextual integer-literal semantics, unsafe-trait obligation ownership,
ordinary-versus-unsafe function calls, call transfer, and the exact
`get_unchecked` safety rule. Each must match the Rust 1.83 proposition catalog.
Do not use the `unsafe impl` declaration as evidence of truth and do not move a
downstream invalid unsafe act into the library's valid-use quantifier.

The closed mode hard errors are exactly `VH1`–`VH6`; common `GH*` and `GD*`
rules apply independently.
