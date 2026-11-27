<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# anneal-scaffold

`anneal-scaffold` writes an identity-keyed Lean module, `AutoScaffold.lean`,
from a capture's `capture.json`. It lives in Anneal's untrusted `tools/` zone,
and its output is an ordinary proof module that Lean elaborates and the kernel
checks like any other, so it adds no trust:

- Each fact about the capture (`found`, `identity_eq`, `isUnsafe_eq`,
  `admitted`, and `params`) is proved by `rfl`, so a stale or wrong scaffold
  fails to elaborate instead of weakening a proof.
- `allBodies_getElem` is a generic lemma about the body list, proved by case
  analysis (`cases`, `injection`, and rewriting). `bodiesVerified` assembles
  its per-body hypotheses into that conjunction in body order and applies
  the lemma, so it elaborates only if the hypotheses cover every captured
  body.
- `defId`, `body`, `identity`, and `fuel` are definitions and assert nothing
  by themselves. `found` and `identity_eq` pin the first three to the
  capture; `fuel` bounds a run only where a proof establishes that it does.

A hand-written `Proof.lean` that names `Captured.body_3` or `DefId` `3` breaks
when the captured bodies are reordered, and one that hard-codes a step count
breaks when a body gains a temporary `let`. The scaffold names each body by
its identity instead. For each body it emits a namespace
`AutoScaffold.b_<slug>`, where the slug is the identity with the
`rust-path-v1::` prefix dropped, each run of other characters replaced by
`_`, and `b_` prepended. Identities that map to the same slug are numbered
`<slug>_1`, `<slug>_2`, and so on in identity order, skipping any name that
is another identity's slug, so every slug is unique and depends only on the
set of identities. The namespace holds:

| Name | Meaning |
|---|---|
| `defId`, `body`, `identity` | the body's `DefId`, `Captured.body_<n>`, and identity |
| `found` | `getElem? Captured.program.bodies defId = some body` |
| `identity_eq`, `isUnsafe_eq` | the body's identity and safety bit |
| `admitted` | `BodyStaticAdmitted` (or `BodyStaticAdmittedV2`) for the body |
| `params` | the body's parameter types |
| `fuel` | for an acyclic body, its number of statements and terminators |

`AutoScaffold.bodiesVerified` turns one hypothesis per body, named
`h_<slug without b_>`, into the per-body obligation of `ProgramVerified` or
`ProgramVerifiedV2`, through a `List.foldr` conjunction in body order that
also scales to sharded captures. Pass the hypotheses by name, so their order
does not matter:

```lean
exact AutoScaffold.bodiesVerified
  (h_usize_as_PointerMetadata_from_elem_count := from_safe)
  (h_usize_as_PointerMetadata_to_elem_count := to_safe)
```

## Usage

```text
anneal-scaffold --capture capture.json --out AutoScaffold.lean
anneal-scaffold --capture capture.json --check AutoScaffold.lean
anneal-scaffold --capture capture.json --out Scaffold.lean --module Proof.Scaffold
```

`--check` exits 1 unless the file already matches byte for byte. `--module`
names the module and its namespace (default `AutoScaffold`). Names under the
roots that `cargo anneal verify` reserves for the model, theory, capture,
claim, and toolchain (`Captured`, `Expected`, `Trusted`, `Anneal`, `Init`,
`Std`, `Lean`, `Lake`, `TrustedBoundary`, and `SpecPreflight`) are refused
before anything is written. Add the scaffold to the unit's `request.json` as
a `proof` source before `Proof`:

```json
{ "module": "AutoScaffold", "path": "AutoScaffold.lean", "role": "proof" }
```

After the captured bodies change, regenerate the scaffold from the new
`capture.json`. The output depends only on the capture, and bodies appear
sorted by slug. Reordering bodies therefore changes only the indices and,
inside the proof of `bodiesVerified`, the order of the `h_<slug>` lines,
which follow capture order because the conjunction they build does. The
`b_<slug>` names and `bodiesVerified`'s parameters, which are sorted by
slug, stay the same, so a proof that passes the hypotheses by name needs no
change.
