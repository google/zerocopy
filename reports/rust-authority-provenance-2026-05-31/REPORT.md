# Rust authority and provenance obligations at the May 2026 source snapshot

## Summary

A Rust safety argument needs both language rules and operation-specific library contracts. The pinned Reference states that unsafe semantics and aliasing remain incomplete; the pointer API nevertheless supplies concrete provenance obligations. Address equality cannot replace those obligations. A certificate that lowers a pointer to an integer or index must retain, reconstruct, or explicitly assume the authority to access the corresponding allocation.

## Applicability

This report examines `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` and pointer contracts/source in `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, matching the existing corpus's May 2026 toolchain subject. UCG at `d809f91e62968913d808e53397fbcf7cea762cce` explains its own role. WG14 N2364 is a separate April 2019 C-model proposal used for comparison; it supplies no Rust authority or interoperability theorem. No compiler or pointer program was executed.

## Findings

### Authority is specific to the claim

| Source | What it can justify | Limit to preserve |
| --- | --- | --- |
| Rust Reference | Published language requirements, including UB prohibitions | Its UB inventory is non-exhaustive; exact aliasing and the full memory model remain unresolved |
| Standard-library safety contracts | Preconditions and guarantees for the named API | A contract for one operation does not define every cast or every aliasing interaction |
| Compiler source or a compiled execution | Behavior of the identified implementation and configuration | Implementation evidence does not resolve a disagreement with the Reference by itself |
| UCG discussion and experimental interpreters | Research context and concrete candidate semantics | UCG points to the Reference and t-opsem FCPs for consensus; Miri's model and coverage are qualified |

The Reference identifies itself as the primary language reference, separates library documentation, and says observed compiled behavior must conform. Its memory chapter includes initialized bytes with optional provenance and uninitialized bytes while warning that the model is incomplete. Thus a plain `List<u8>` can be a useful abstraction only after a relation accounts for discarded initialization and provenance state. Basis: **normative** Reference + **derived** abstraction obligation. [Introduction](https://github.com/rust-lang/reference/blob/ad35aca481751a06afeb23820a672b0f3b11a476/src/introduction.md), [memory model](https://github.com/rust-lang/reference/blob/ad35aca481751a06afeb23820a672b0f3b11a476/src/memory-model.md).

### Strict APIs identify the information a representation change must preserve

| Operation | Contract relevant to a certificate |
| --- | --- |
| `p.addr()` | Returns an address, discards provenance, and does not expose it; a cast back does not thereby acquire access authority |
| `p.with_addr(a)` / `map_addr` | Uses the original pointer's provenance with a changed address; access still requires that provenance to authorize the resulting range |
| `p.expose_provenance()` / pointer-to-integer `as` | Returns an address and exposes provenance for possible later reconstruction |
| `with_exposed_provenance(a)` / integer-to-pointer `as` | Does not name the chosen provenance; the documented model does not guarantee which eligible provenance is selected |
| `offset(n)` | For a nonzero byte offset, requires allocation derivation and an in-bounds intervening range; mathematical byte offset must fit `isize` |

The implementation of `with_addr` uses wrapping byte offset, preserving provenance. The implementation of `addr` uses a pointer-to-integer transmute, but its comment explicitly limits that equivalence to the current privileged sysroot implementation; it does not establish ordinary Rust transmute semantics. Basis: **normative** API contracts + **source** implementation. [Pointer methods](https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/const_ptr.rs#L149), [addr contract](https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/docs/addr.md), [offset contract](https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/docs/offset.md).

The module contract describes spatial, temporal, and mutability components. A deallocated allocation's address being reused does not revive a stale pointer's access rights. Equal addresses can belong to pointers with different provenance. The exact provenance structure remains unsettled. Basis: **normative** API documentation. [Provenance](https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L146).

### C provenance work exposes a semantic choice rather than an interchangeable model

N2364 distinguishes PVI, whose integers also carry provenance, from PNVI variants, whose integers are numerical values. PNVI-ae reconstructs provenance only from exposed live storage; PNVI-ae-udi adds symbolic choice for ambiguous one-past addresses. Its exposure events include reading pointer representation through a non-pointer type and `%p`, beyond a pointer-to-integer cast. The proposal's state records storage-instance identity, lifetime, address, permissions, and exposure, separately from abstract bytes. These are design alternatives, not a proof that Rust exposed provenance implements PNVI-ae-udi. N2364 omits linking and some I/O construction and simplifies other C details. Basis: **source**, N2364 §§1–3. [N2364](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n2364.pdf).

### A certificate must relate authority, not just address arithmetic

For a source pointer `p` related to a model reference `(allocation, offset)`, a load proof needs to connect the model allocation to the source allocation instance, preserve its lifetime, and establish source access permission for the requested range. Index bounds and numerical address equality establish only part of that relation. Aliasing changes may revoke access while leaving both numbers unchanged.

If the model retains a source pointer as the witness used by `with_addr`, it must establish that this witness still has sufficient provenance at the access. If it relies on exposed reconstruction, it must record the exposure event and the chosen semantics' admissibility condition. If it erases provenance entirely, it owes a theorem that the admitted program fragment never needs the erased distinctions. These alternatives are **derived obligations**, not a proposed universal certificate schema.

## Boundaries

- **Unknown:** a complete normative operational interpretation of exposed provenance or Rust aliasing. No claim that a particular integer round trip is justified merely by arithmetic equality.
- **Not examined:** exhaustive t-opsem decisions, FFI linking, MMIO, CHERI, allocator behavior, target-specific pointer representations, and const-evaluation casts.
- **Known not to apply:** N2364 is a C research proposal; its reconstruction and pointer-comparison rules cannot be imported as Rust rules.
- **Not established:** a source-to-model certificate, a semantics-preserving lowering of any zerocopy function, or soundness for a new configuration. The obligations above identify what such evidence must provide.

## Evidence

Acquired on 2026-10-14 by direct pinned-source retrieval. Language/API requirements are **normative**; implementation observations are **source**; certificate implications are **derived**.

- Reference: full commit above, `src/introduction.md`, `src/memory-model.md`, `src/behavior-considered-undefined.md`, especially the incomplete-semantics and aliasing qualifications.
- Rust: full commit above, `library/core/src/ptr/mod.rs`, `Provenance`, `Strict Provenance`, `Exposed Provenance`; `const_ptr.rs:149–235`, `addr`, `expose_provenance`, `with_addr`, `map_addr`; `ptr/docs/addr.md` and `ptr/docs/offset.md`.
- UCG: full commit above, `README.md`, role of the archived book and t-opsem consensus. [Pinned README](https://github.com/rust-lang/unsafe-code-guidelines/blob/d809f91e62968913d808e53397fbcf7cea762cce/README.md).
- WG14 N2364, dated 2019-04-01: §§1–3, distinct integer/pointer domains and allocation/exposure state. Its document identifier and date bind the examined proposal; no claim of present C standard status is made.
- Existing corpus context was read at `a0ff759e7d2d9a953f0ac40b326dd23197bd9188`, especially the UB/operational-model and raw-pointer provenance reports. The findings above were checked against primary sources.

## Revalidation

For another Rust snapshot, diff the named Reference clauses and pointer contracts together. Check the source behind `addr` and `with_addr`, keeping implementation-only comments separate from public guarantees. For a proposed lowering, test two pointers with equal addresses but distinct allocation histories, and distinguish `addr` from exposure. A passing example cannot establish universal reconstruction. For a C/Rust composition claim, first select exact C and Rust models, then prove the relation across their exposure, lifetime, and byte rules.

*Authored by an AI agent acting on joshlf's behalf.*
