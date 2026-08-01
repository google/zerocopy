# Source-only unsafe Rust audit

## Claim, snapshot, and domain

This audits exactly the four exported unsafe functions in `target/lib.rs`, under their published caller contracts, for absence of Rust undefined behavior and every documented postcondition. The snapshot is the submitted `lib.rs`, `SUPPORT.md`, `EVIDENCE.md`, and `TCB.md`; no generated code, dependencies, tools, builds, or execution are involved. Audit cutoff: 2026-07-31. TCB revision: the submitted `TCB.md`.

`SUPPORT.md` expressly defines complete finite sets, so no interval inference is used:

- `V_ack = {1.80.0, 1.80.1, 1.81.0, 1.82.0}`
- `V_store = {1.80.0, 1.81.0}`
- `V_copy = {1.80.0, 1.80.1, 1.81.0, 1.82.0}`
- `V_load = {1.80.0, 1.80.1, 1.81.0, 1.82.0}`

For each, `Required` is its exact release set crossed with every target where the item exists, every ordinary debug/release profile, and every call satisfying its documented safety obligations. The explicit completeness statement proves equality between each list and its `Required` release projection. There is no `cfg`, generator, feature, or profile-dependent source. Target/profile coverage below is parametric: the cited abstract operation contract is unqualified over those axes, or the accepted TCB entry expressly quantifies over them.

## Verdict ledger

| API / component | Exact `Covered` release region | Regional and full-domain verdict |
|---|---|---|
| `acknowledge` soundness | `V_ack` | **PROVED** on `V_ack` |
| `acknowledge` postconditions | No prose postcondition; unit return is covered on `V_ack` | **PROVED** for the signature-implied `()` return |
| `store_word` soundness | `V_store` | **PROVED** on `V_store` |
| `store_word`: destination contains `value` | `V_store` | **PROVED** on `V_store` |
| `store_word`: old `u16` is not read | `V_store` | **PROVED** on `V_store` |
| `store_word`: old `u16` is not dropped | `V_store` | **PROVED** on `V_store` |
| `copy_byte` soundness | `V_copy` | **PROVED** on `V_copy` |
| `copy_byte`: destination byte equals the pre-call source byte | `V_copy` | **PROVED** on `V_copy` |
| `copy_byte`: source byte is preserved | `V_copy` | **PROVED** on `V_copy` |
| `load_word` soundness | `{1.80.0, 1.82.0}` | **PROVED** there; **UNPROVED** on `{1.80.1, 1.81.0}`; full `V_load`: **UNPROVED** |
| `load_word`: return equals the initialized pre-call source `u32` | `{1.80.0, 1.82.0}` | **PROVED** there; **UNPROVED** on `{1.80.1, 1.81.0}`; full `V_load`: **UNPROVED** |
| `load_word`: source remains unchanged | `{1.80.0, 1.82.0}` | **PROVED** there; **UNPROVED** on `{1.80.1, 1.81.0}`; full `V_load`: **UNPROVED** |

Thus the strongest combined per-API verdicts are: `acknowledge` **PROVED**, `store_word` **PROVED**, `copy_byte` **PROVED**, and `load_word` **UNPROVED**. The combined four-API packet is **UNPROVED**. No submitted fact proves an existential UB execution or an UB-free postcondition counterexample, so neither **UNSOUND** nor **CONTRACT-BROKEN** is certified.

## Proof certificates

### `acknowledge`

The inspected signature has no parameters, returns `()`, documents no additional caller obligation, and its body is exactly `{}`. Accepted `SEM-EMPTY-BLOCK-180-182` says precisely that, for every case in `V_ack` and the required target/profile axes, such evaluation is defined and returns `()`; `unsafe` only adds the static call obligation. The entry is restricted to this consumer. Hence aggregate `Covered = V_ack`, so `Required ⊆ Covered`.

### `store_word`

The only operation is `ptr::write::<u16>(dst, value)`. The caller contract supplies its two safety clauses: `dst` is properly aligned and valid to write one `u16`. The exact [1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.write.html) and [1.81.0](https://doc.rust-lang.org/1.81.0/std/ptr/fn.write.html) authorities make those the operation requirements and specify overwrite with the supplied value without reading or dropping the old value. One authority applies to each member of `V_store`; their exhaustive union covers every required release. The source has no other operation or exit. Each soundness and postcondition obligation therefore has `Covered = V_store`, and their pointwise intersection is `V_store`.

### `copy_byte`

The source fixes `T = u8` and `count = 1`; its caller contract supplies readable initialized source, writable destination, alignment, and non-overlap. The accepted `COMPAT-COPY-180-182` entry preserves, for every `v ∈ V_copy` and required target/profile case, the exact 1.80.0 propositions for this operation: satisfaction of the safety contract, copying exactly one byte to `dst`, and leaving `src` unchanged, with `u8` size 1 and `Copy` semantics. Its verified bases are [`copy_nonoverlapping`](https://doc.rust-lang.org/1.80.0/std/ptr/fn.copy_nonoverlapping.html), [layout](https://doc.rust-lang.org/1.80.0/reference/type-layout.html#primitive-data-layout), [`u8: Copy`](https://doc.rust-lang.org/1.80.0/std/primitive.u8.html#impl-Copy-for-u8), and [`Copy`](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html). The TCB expressly restricts consumption to `copy_byte`. Thus every obligation has `Covered = V_copy`; their intersection equals `Required`.

### `load_word`

The only operation is `ptr::read::<u32>(src)`. At 1.80.0 and 1.82.0, the caller supplies the cited operation's readable, aligned, initialized-source requirements. The respective [`read` 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.read.html) and [`read` 1.82.0](https://doc.rust-lang.org/1.82.0/std/ptr/fn.read.html) pages establish returning the read value while leaving source memory unchanged; the corresponding [`u32: Copy` 1.80.0](https://doc.rust-lang.org/1.80.0/std/primitive.u32.html#impl-Copy-for-u32), [`Copy` 1.80.0](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html), [`u32: Copy` 1.82.0](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#impl-Copy-for-u32), and [`Copy` 1.82.0](https://doc.rust-lang.org/1.82.0/std/marker/trait.Copy.html) discharge the copy/ownership bridge at those endpoints.

No authority or accepted TCB entry applies these propositions to 1.80.1 or 1.81.0. Endpoint documentation, stability, and unchanged-looking source cannot supply semantic continuity. The smallest missing premise is: for each missing release and all required target/profile cases, `ptr::read::<u32>` retains the cited safety and result/source-preservation contract and `u32` retains the cited `Copy` semantics. Consequently `Covered = {1.80.0, 1.82.0}`, which does not contain `V_load`.

## TCB, proof artifacts, and residual scope

The only admitted non-authoritative premises are accepted OUT-OF-BAND entries `SEM-EMPTY-BLOCK-180-182` (consumer: `acknowledge`) and `COMPAT-COPY-180-182` (consumer: `copy_byte`). Their exact scopes, exclusions, and source/signature/contract/domain/disposition re-audit triggers are retained from `TCB.md`; neither is transferred to another API. All other consumed premises are the exact claim-specific versioned Rust pages above. No pending premise was used.

The adjacent `SAFETY` comments correctly identify caller-contract forwarding but omit the material release-applicability and postcondition derivations reconstructed here. They should cite a canonical proof containing the exact authority/TCB entry and covered set. For `load_word`, comment wording cannot repair the missing 1.80.1/1.81.0 premise; resolution requires applicable authority or an explicitly accepted narrow compatibility entry.

Re-audit on any source/signature/contract change, any supported-set or configuration expansion, material change to a cited page, or change to either TCB entry/disposition. Releases outside the four explicit predicates, binary/backend correctness, and broader robustness are excluded.
