# zkVM receipt binding and verification boundaries

## Summary

A zkVM receipt can establish execution of identified machine code on some admitted inputs, under cryptographic and circuit assumptions. It does not independently prove that this code implements the desired checking relation or faithfully translates Rust. The inspected RISC Zero and SP1 normal verification paths bind program identity, public outputs and execution status; their development/mock paths provide deliberately weaker evidence. Private input identity, parser meaning, verifier configuration and recursive proof assumptions must remain explicit.

## Applicability

Implementation observations apply to risc0/risc0 3bbcd44d6459b9ef6ac0df3846dc9215514934e8 and succinctlabs/sp1 02fa30185ecd658174b211d56128b14867ab8e81. These are exact inspected repository heads, not releases or installed SDK binaries. RISC Zero API 3.0 documentation and its August 11,2023 draft whitepaper are independently identified subjects; continuity to every current circuit is not assumed.

The comparison addresses T050–T052/P116 as mechanism and trust-boundary research. No proving, receipt verification execution, circuit build, setup transcript validation, deployment or cost measurement was performed. Selected APIs and source checks were read directly.

## Findings

### RISC Zero: the standard expected claim

**Basis: source.** risc0/zkvm/src/receipt.rs:152–193 first verifies integrity with the selected context, then compares the inner claim digest to ReceiptClaim::ok(expected image ID, journal digest). The standard success endpoint differs from verify_integrity_with_context, whose documented contract at196–206 does not constrain the image or successful exit. Calling the weaker method alone does not bind the application's expected program.

claim/receipt.rs:75–94 makes the expected claim precise: the supplied pre-image digest; a final zeroed SystemState; Halted(0); input=None; and an Output containing the supplied journal and zero unresolved assumptions. Thus standard verification binds successful completion and an unconditional journal claim, not an arbitrary conditional execution claim.

The input field at406–422 is currently uninhabited; the standard claim does not independently commit to the original private input bytes. A checker guest should explicitly commit the required source/certificate/configuration digests or public inputs if the application needs that identity. Otherwise the meaningful claim can remain existential over admissible private inputs.

### Image identity and journal identity have distinct roles

**Basis: source.** risc0/binfmt/src/image.rs:297–300 updates the image Merkle tree and returns its root digest. The inspected method identifies the loaded image representation; the entire ELF loader, entry-state construction and build chain were not audited. The expected image identifier must come from the independently selected guest, rather than simply accepting an identifier supplied alongside an untrusted receipt.

The journal bytes are part of the claim through their digest. A successful proof of a checker guest that committed a Boolean says only what that guest computes under its implemented semantics. If its output is meant to certify a particular source/model pair, the bytes must additionally identify that pair and the format/schema version.

**Basis: derived.** Hash binding prevents substituting different committed artifacts under the assumed hash properties. It does not make a correctly identified parser or checker semantically sound. Authentication and execution evidence cannot repair a predicate that accepts the wrong relation.

### Recursive assumptions and control programs must be discharged

**Basis: source.** claim/receipt.rs:426 onward records recursive verification assumptions in the Output. Its documentation explains that nonempty assumptions do not yield an unconditional genuine-execution claim. The standard ok claim expects zero assumptions; integrity-only verification does not substitute for that discharge.

receipt/succinct.rs identifies an allowed recursion program by control_id and verifies its Merkle inclusion under a trusted parameter control_root (153 onward). It also compares the root carried in the seal's public output with the expected root (179–198). Groth16 receipts use context-selected verifier parameters and a verifying key; the accompanying receipt metadata is not a reason to trust an arbitrary verifier configuration.

The root/key is an identity boundary for the circuit/recursive verifier being relied on. Changing it can change the accepted language of proofs even when the guest image stays fixed. A protocol must identify both the guest computation and the trusted verification configuration.

### Development receipts preserve structure while skipping integrity

**Basis: source plus API 3.0 documentation.** FakeReceipt::verify_integrity_with_context at receipt.rs:589–599 returns Ok in a dev context and rejects otherwise; disable-dev-mode guards that acceptance. VerifierContext supports environmental or explicit dev-mode selection. A matching fake claim can therefore pass surrounding claim-binding checks without cryptographic evidence. The public journal and expected image fields do not turn that mock into a proof. [Official dev-mode description](https://dev.risczero.com/api/generating-proofs/dev-mode).

No development mode was executed. The documented panic when a disabled build is asked to enable dev mode is a source/configuration boundary, not an observed panic. An assurance gate should identify the actual verifier context and build features, rather than infer soundness from the receipt type or successful API return alone.

### SP1: normal status, version and public-value checks

**Basis: source.** crates/sdk/src/prover.rs:143–262 checks the proof's circuit-version string, defaults the accepted status to success unless a caller selects another StatusCode, and validates the committed public-value digest. Core/compressed variants accept the supported SHA2 or Blake3 digest convention; Plonk/Groth16 variants parse the public input digest and status. It then invokes node.verify with the selected verifying key and proof.

crates/prover/src/verify.rs independently validates core shard/public-value structure and delegates the SNARK variants through expected key/public-value commitments and bundled verifier keys. These are source observations of checks, not a newly proved theorem that the complete AIR and verifier implement the intended ISA.

The application must still compare or decode the public values for its intended claim. Successful SP1 execution with the selected status does not by itself mean an embedded checker returned acceptance, identified the correct source artifacts, or used a sound checking predicate.

### SP1's verifying-key hash binds machine configuration

**Basis: source.** crates/hypercube/src/verifier/hashable_key.rs:105–127 hashes the preprocessing commitment, initial PC, initial global cumulative sum and enable_untrusted_programs. Under mprotect it also includes trap-handler and untrusted-memory configuration. This is richer than a hash of a human-readable program filename.

crates/hypercube/src/air/public_values.rs identifies the committed-value digest as the hash of guest public bytes and a deferred-proof digest that is rebuilt during recursive verification. The relation between preprocessing and the actual ELF, complete AIR obligations and deferred-proof closure requires the selected compilation/verification route. This investigation did not audit all such constraints.

### SP1 mock verification is deliberately weaker

**Basis: source.** crates/sdk/src/mock/mod.rs:88–109 ignores the requested status argument. For mock Plonk/Groth16 it calls verify_mock_public_inputs, which checks only the expected verifying-key hash and public-values hash (proof.rs:22–47); the encoded proof is absent. Other proof variants return Ok. This path supplies neither cryptographic integrity nor the normal status guarantee.

Mock proving may execute a guest for development, but arbitrary mocked data and matching public hashes are not execution certificates. These facts are scoped to the selected mock implementation, not a claim that normal SP1 verification omits its status or integrity checks.

### Cryptographic soundness and circuit correspondence are separate

**Basis: primary RISC Zero whitepaper.** The August 2023 draft treats execution validity as satisfaction of polynomial constraints and analyzes the interactive-oracle protocol, then applies Fiat–Shamir in a random-oracle model. Its §3.4 distinguishes proven list-decoding-range bounds from conjectured extensions and combines the constituent argument errors. That analysis concerns the stated protocol; it does not mechanically prove every current implementation constraint or Rust compiler route. [Draft whitepaper, §§2.1/3.4](https://dev.risczero.com/proof-system-in-detail.pdf).

**Basis: official security documentation.** The API 3.0 security model lists random-oracle/Toy-Problem assumptions for STARK provers and pairing, knowledge-of-exponent and ceremony integrity assumptions for the Groth16 wrapper. Its setup account separately requires that circuit, compiled constraints and setup transcript correspond. This report makes no numerical security or proof-cost estimate. [Security model](https://dev.risczero.com/api/security-model), [Setup description](https://dev.risczero.com/api/trusted-setup-ceremony).

SP1's pinned code exposes core, compressed and SNARK verification layers. Its complete current mathematical security argument, ceremony/key identity and AIR-to-ISA formal correspondence were not independently resolved in this bounded wave. The mechanisms may be compared under explicit assumptions; an audit label or proof-system name is not a substitute for those missing artifact-specific claims.

### Derived Anneal execution proposition

A useful receipt-backed checker claim would have the form: identified guest G, identified input artifacts A and configuration C, successful normal execution, and public acceptance output, together with an independent theorem that G accepts only when the required relation over A/C holds. The guest must also establish the admission properties expected by that theorem, including decoding, reference resolution, arithmetic and failure handling.

The receipt can replace repeating the execution only after these propositions and identities are connected. It cannot replace proof of the checker algorithm, its implementation, or the compiler/ISA/circuit bridge. Hiding certificate bytes as private inputs is compatible with a useful claim only when their relevant public commitment and relation to the specified artifacts are themselves established.

Maintenance includes image construction, verifier version/context, allowed control roots, proving/verifying keys, public-value encoding, exit-status conventions, dependency/configuration identity and mock/dev feature policy. Reusing a receipt across any of these changes requires an explicit compatibility argument. Actual proof generation cost, verifier cost and comparison with kernel checking remain measurement questions.

## Boundaries

No receipt, guest binary or setup artifact was generated or verified. No all-constraints audit or circuit-to-ISA formal proof was inspected. Neither repository pin identifies an installed executable or released verifier key by itself. The 2023 protocol paper and API 3.0 documentation are not treated as proof of every current repository path.

Private inputs are not automatically bound merely because a journal or vkey is bound. Integrity-only verification, unresolved assumptions, custom accepted status, fake receipts and mock verifiers have weaker guarantees. Source correctness, public-output interpretation, Rust safety and faithful extraction remain separate from cryptographic execution.

## Evidence

- RISC Zero full pin in metadata: receipt.rs blobfb00ecbdde3eb3ebc10e2440d8547099edd47ee8, verify:152–193/integrity contract:196–206/FakeReceipt:589–599/VerifierContext:897–1002; claim/receipt.rs blob 5018e5e84d34a775a283b8193472272e8496d8e2, ok:75–94/assumptions:426 onward.
- RISC Zero binfmt image.rs blob 953ec2e39fc0376fc80a4dee4705d336b4536c85; receipt/succinct.rs blob 8c5d4be82cd71784a81ce3a6ad0699293bbe7a04; receipt/groth16.rs blobdba951e3b04aed6cc4e0935c60acbfadf8bc5155. Paths are beneath risc0/zkvm/src except image.rs beneath risc0/binfmt/src.
- SP1 full pin in metadata: crates/sdk/src/prover.rs blobe58cb58301c66642b2009707a323425d2c2c50aa; mock/mod.rs blobea937abba29550c263a350f66139bf2c372d7891; proof.rs blob 78ae3e8e05b748aba33eefe817234e570da05fca; crates/prover/src/verify.rs blobaebbc97fecaa5d9aff6a0d46a477c2d26fd4c03b.
- SP1 crates/hypercube/src/verifier/hashable_key.rs blob 86c4a06bd3d3644ecbfd878124bdaab68297cefe; crates/hypercube/src/air/public_values.rs blob 38c95cfffccefc75fd26a8b4ca8b6eeee7c09e1a.
- RISC Zero draft whitepaper 35 pages, August 11,2023: §§2.1/3.4, PDF pp7/13–14. Official security/dev/setup pages identify API 3.0. Public primary evidence acquired 2026-10-14. No immutable PDF byte identity, source mirror, execution or measurements stored.

## Revalidation

Re-fetch the pinned regions and inspect actual verifier configuration and proof mode. Check expected guest ID/key, status, journal/public-value interpretation, recursive assumption closure and trusted circuit parameters independently. Before deployment, acquire exact guest/compiler/verifier/key artifacts and an applicable circuit/ISA/security argument. Run real-mode negative checks for wrong program, wrong public values, unsuccessful status and unresolved assumptions; mock-mode success cannot validate those guarantees.

*Authored by an AI agent acting on joshlf's behalf.*
