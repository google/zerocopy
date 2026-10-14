# Zerocopy public byte APIs: exhaustive small domains and write preservation

## Summary

At PR-stack revision `cce761ad53785973ec2f4a6b13715b770b340c87`, safe public Boolean reads accept exactly zero/one in all 256 one-byte inputs and exactly four valid pairs among all 65,536 two-byte inputs. Additional controls check width, zero-sized arrays, byte order, alignment and preservation of untouched destination bytes or rejected writes.

These actual-crate observations supply a reusable small evaluation workload. They do not prove universal unsafe-Rust safety or the validity of every internal pointer operation. Their initialized safe slices and fixed native target deliberately leave provenance, padding, concurrency and arbitrary caller-state correspondence open.

## Applicability

The driver materializes `git archive cce761ad53785973ec2f4a6b13715b770b340c87 zerocopy` privately; its retained SHA-256 is `5097beee2b15db9c83171f75feacd857a4529392f926531792c4655f8ac1c48f`. Cargo resolves the path dependency from that materialization, with no explicitly enabled crate features, edition 2024 for the owned harness, the default development profile, and `--offline --quiet`. The crate manifest identifies version 0.8.63. The test is not against a registry crate with the same version.

The compiler reports Rust 1.99.0 commit `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, AArch64 macOS and LLVM 23.1.1. This differs from Anneal's extraction compiler. `Cargo.lock`, input hash, command statuses and output are retained. All owned harness operations are safe Rust; the crate's internal unsafe implementations remain part of what the API observations exercise.

Agenda scope: R095/P131 receive an actual byte-validator workload; P138/R005 receive one native configuration rather than the requested cross-target matrix. R061/P083/P084 receive narrow representation and write observations without a runtime semantics proof.

## Findings

### Raw invalid encodings remain in the tested domain

The harness passes every `u8` value to `bool::try_read_from_bytes`. Acceptance agrees exactly with `byte <= 1`, and accepted values agree with the zero/one Boolean interpretation. It also enumerates every pair for `[bool;2]`; a pair is accepted exactly when both bytes are zero or one, preserving their order.

The independent expected predicate is authored directly in the owned input, rather than obtained by calling the library's validity helper. This separates implementation output from its expected finite domain. All inputs are ordinary initialized byte arrays; invalid Boolean encodings are never first constructed as Boolean values by the harness.

The inspected implementation uses `util::validity::bool_encoding` through a byte-level view before constructing a valid Boolean. The execution corroborates its public read behavior, not a formal proof of that view's access authority or every possible aliasing history.

Basis: **execution**, complete enumeration; **source**, `zerocopy/src/impls.rs:103–117` and public `try_read_from_bytes`; **derived**, coverage boundary.

### Width and initialization do not disappear behind a decoded value

Empty and two-byte inputs reject a scalar Boolean read. Three unit elements accept an empty representation and reject an extra byte. These examples preserve the distinction between element count and byte length.

Every test input is initialized by safe Rust construction. Consequently no result establishes acceptance or rejection of uninitialized padding or poison. Those require an operational model, a suitable abstract-machine test, or a separately justified unsafe harness with explicit valid access premises. The companion pure-model report checks an uninitialized mathematical byte without executing invalid Rust.

Basis: **execution** + **derived** scope.

### Byte order and alignment are separate contracts

`U16<LE>` reads `[1,0]` as one and `U16<BE>` as 256. A safely initialized `[u64;2]` supplies a byte region; eight offsets are tested with `u16::ref_from_bytes`. Success agrees with the actual numerical address's divisibility by `align_of::<u16>()` for each fixed-width slice.

That alignment observation begins from an existing live, readable slice. It does not establish that an arbitrary address with the same divisibility has provenance, allocation membership or permission. The address conversion is used only to state the expected alignment; no pointer is reconstructed from the integer.

Basis: **execution**; **derived**, separation of alignment and authority.

### Writes preserve the unselected region and rejection state

A four-byte source written to a six-byte destination replaces the prefix or suffix and retains the two other bytes. Attempting the prefix write into a three-byte destination returns an error and retains all three destination bytes.

This makes result values, destination updates and rejection effects distinct expectations. A model comparing only successful return values would miss the preservation properties. The tested data is padding-free, initialized and disjoint; no ownership transfer, overlapping copy or runtime padding law is established.

Basis: **execution**, `main.rs` assertions; **derived**, contract observation requirements.

## Boundaries

- **Not established:** a proof-assistant certificate, Rust semantic adequacy, all unsafe implementation accesses, all valid callers, or arbitrary byte-bearing types.
- **Not examined:** other targets/toolchains, optimizer profiles, ABI flags, full Cargo configuration capture, Miri, formal extraction or abstract-machine correspondence.
- **Not established:** initialized padding, pointer-bearing representation, provenance round trips, typed moves, drop behavior or concurrent interference.
- The finite domains are fully enumerated for this harness. This does not make the observed implementation safety or the compiler itself formally verified.
- No performance claim or cross-tool benchmark is made.

## Evidence

- **source:** [exact crate source](https://github.com/google/zerocopy/tree/cce761ad53785973ec2f4a6b13715b770b340c87/zerocopy), particularly `src/lib.rs`, `src/impls.rs`, `src/util/validity.rs` and byte-order implementations.
- **execution/source:** `support/main.rs`, hash recorded in `support/results.json`; immutable source archive selection and hash.
- **execution:** retained `rust-version.stdout.txt`, `cargo-run.stdout.txt`, stderr, statuses, and resolved `Cargo.lock`; both recorded commands succeed.
- **derived:** comparison requirements and stated semantic exclusions.

## Revalidation

Run `python3 -B support/run_probe.py /path/to/zerocopy-clone` with the named compiler available and dependencies already cached. The driver recreates the exact source archive, uses a private target directory, and requires offline Cargo success. A compile/setup failure is an operational result; it does not establish domain rejection.

Inspect the version, source/input hashes and all assertions. For a wider evaluation, add exact configurations and use the same independently authored expectations. Add structured padding, mutable projection and invalid-production controls only with a model or harness that represents their access and initialization obligations soundly.

*Authored by an AI agent acting on joshlf's behalf.*
