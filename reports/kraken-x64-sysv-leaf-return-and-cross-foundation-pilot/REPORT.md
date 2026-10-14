# Checked X64 addition, stack return, full frame, and byte-bound comparison

## Summary

A fresh Kraken X64 proof checks the actual program `leaq (%rdi,%rsi,1), %rax; ret` for every initial modeled state and supplied layout. Given an eight-byte return-address cell at RSP, it returns the wrapping sum of RDI and RSI in RAX, advances RSP by eight, restores the loaded return-PC bits, and preserves every other field of MachineData, including flags, ZMMs, and the entire byte map. The proof covers the complete modeled return path, not only the arithmetic body.

An actual hidden-RBX-clobber program is proved incompatible with that frame, and an incorrect return-PC contract is refuted. A separate checked interpretation characterizes the leaf's exact emitted access obligations: two execute ranges and one eight-byte stack read, with no write request. Seven permitted stack bytes are insufficient even when the byte-map load succeeds.

The package also rechecks a preserved AArch64 peer proof and the actual s2n-bignum ELF byte comparison. All 20 selected semantic declarations have exactly `propext`, `Classical.choice`, and `Quot.sound` in their printed closure; an additional checked host-program identity uses no axioms. The s2n comparison matches all 185 proof-literal bytes and rejects byte/target/symbol mutants; it does not replay HOL Light. The common comparison is the mathematical low-64-bit sum under explicit observation mappings, not interchangeable ABI behavior between the two routines.

## Applicability

The model is Kraken `8af78062037bc237b341d20252aafd1797c1bcb7`, both X64 and AArch64. Checks use installed Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, against the read-only library built from that source. Kraken requests `nightly-2026-09-21`; this remains an explicitly different toolchain observation. No compiler, native assembly, or Rust execution was added in this package.

The X64 interface is SysV-shaped: two unsigned word arguments are represented by RDI/RSI and the result by RAX, with a return address read from RSP. This is an exact register/memory contract, not a complete formalization of the System V ABI. Stack alignment, canonical addresses, VM mappings, caller state/resources, and deployed-code identity require additional premises and correspondence evidence. LEA was selected because this model leaves flags unchanged while computing the sum.

The preserved AArch64 peer is byte-identical to the parent-authored `KrakenPilot.lean` input, copied as `support/AArch64Peer.lean` and freshly checked here. It uses `add x0,x0,x1; ret`, returns through X30, and preserves all modeled data except X0. The native Rust and Mach-O work elsewhere in the parent workflow was not repeated and is not evidence claimed by this package.

The s2n subject is `awslabs/s2n-bignum@4d1356a7470663c752660a59375dc3a9ef548428`, standard non-Windows x86-64 ELF with default IBT. Its small source/header/object and exact build provenance remain in the public first-wave companion package and were independently byte-checked here through that relative companion path. This package answers an actual local composition/pilot slice of AS17/AS28 and a program-level arithmetic comparison relevant to AS04. It does not close Kraken-to-independent-ISA refinement.

## Findings

### The return theorem has a complete modeled frame and a real stack witness

`X64Pilot.lean` defines `bodyState d` by changing only RAX to `d.rdi + d.rsi`, and `returnState d` by additionally changing RSP to `d.rsp + 8`. These are full structure updates, so equality to them preserves every unlisted general register, every modeled vector register, status flags, and memory.

`addBody_correct` proves the body's exact MachineData result. `addReturn_correct` proves:

```text
d.dmem =⋆ Eq (returnAddress.At d.regs.rsp.toBitVec) ⋆ R
  → straightlineStep (layout addReturn) (d, layout.start)
      (fun final => final.data = returnState d
                  ∧ final.pc.toBitVec = returnAddress.toBitVec)
```

The return address is an arbitrary UInt64; the theorem does not accidentally require its high bit to be zero. The separation premise contains its eight little-endian bytes and an arbitrary disjoint remainder. `Mem.loadInt_sep` derives the actual load result. The generic `addReturn_of_load` uses an arbitrary decoded Int, and the wrapper applies the checked byte round-trip lemma to recover all 64 return bits. Since the final memory equals the initial memory, the same byte-map decomposition and every predicate of that map remain true. No Rust provenance or borrow assertion is encoded by that observation.

Kraken's source defines RET by loading W64 at the current RSP, branching to those bits, and updating RSP by eight. LEA calls `setReg` without changing flags or loading memory at its computed address. The proof unfolds those exact operations and the directive interpreter; the return path does not invoke the noisy memory `kstep` route. [Pinned operations](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/X64/Semantics.lean#L494), [RET](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/X64/Semantics.lean#L744), [stack-byte load lemma](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/SeparationMem.lean#L118).

`addReturn_iff` is stronger than a single postcondition proof: for any supplied postcondition, the whole straightline judgment is equivalent to that postcondition at the exact calculated final state. It is a checked local composition result for the two-instruction list under any layout. It does not embed that list into an arbitrary Host executable, connect `step1` and `straightlineStep` generally, or prove a caller continuation. The return target is the endpoint of this judgment; fetching the caller's next instruction is not included.

Basis: primary **source** + fresh Lean **execution**. The returned state and map-frame consequences are checked or directly **derived** from structure equality.

### A fixed host embedding has checked entry and two-step composition

The new host places the leaf between two NOPs. Its exact parsed program and laid-out directive identity are checked by `fixedHost_program_identity`:

| Directive | Declared address | Declared size |
|---|---:|---:|
| Prefix NOP | 4096 | 1 |
| LEA addition | 4097 | 4 |
| RET | 4101 | 1 |
| Suffix NOP | 4102 | 1 |

`host_addReturn_iff` takes an arbitrary executable plus an explicit equality to this complete `fixedHost`, an initial PC plus the premise PC = 4097, and the return-address load witness. It proves the same exact final-state postcondition characterization as the isolated leaf. Thus the prefix is skipped by entering the proper address, and the suffix is skipped because RET exits the interpreted burst. The equality premise binds start address, directive list, and every size; matching a textual function name alone is insufficient.

Two further lemmas compute actual `step1` judgments at the two distinct instruction addresses: entry executes LEA and reaches 4101 with `bodyState d`; the next step executes RET with the witnessed stack load. `host_two_step_composition` combines these through the baseline `step_cps`/`Eventually` constructors to reach any predicate holding at the specified final state. This is a checked two-step embedding/composition instance, not an assumption that `step1` and straightline judgments always coincide. [Pinned step/list views](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/X64/Semantics.lean#L808), [composition constructor bridge](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/OmniSemantics.lean#L25).

`host_permission_iff` independently calculates the embedded execution's two execute obligations, `[4097,4101)` and `[4101,4102)`, plus the same eight-byte stack read. It does not require access to the unexecuted prefix/suffix. The four declared sizes are model inputs, not a verified encoding/layout witness. These theorems do not generalize to arbitrary relocation, linking, overlapping directives, escaping jumps, or host replacement; changing this host requires a new identity and proof.

### The negative controls are checked semantic propositions

`wrong_return_rejected` proves that, when the required load succeeds, a postcondition demanding different return bits is false under the actual `straightlineStep` judgment. Its explicit side condition excludes the trivial case where the purported wrong bits equal the loaded bits.

`clobberReturn` changes the actual program by inserting `movq $99,%rbx` before RET. `hidden_clobber_rejected` proves this program cannot satisfy the original full data frame whenever initial RBX differs from 99. It permits the scalar RAX sum to be correct; failure follows from the hidden register effect. These are kernel-checked refutations, not expected compiler errors, concrete tests masquerading as universal theorems, or admitted failed proofs.

The initial ordinary proof-development errors are retained in attempt logs. The final file exits zero, and the runner rejects `sorryAx`, native/custom axioms, printer fallbacks, panics, assertion failures, or a missing printed closure. All 18 X64 semantic declarations and both AArch64 peer declarations print exactly the foundational trio; the additional host-program identity prints no axioms. No native `bv_decide` axiom is present.

### The emitted footprint is checked for this actual leaf

Default X64 `Effects.All` ignores permission requests. The owned `PermissionAll` interpretation instead conjoins predicates for each read/write request's byte width and each execute range, keeps undefined choices universal, and rejects modeled errors. [Default interpretation](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/X64/OmniSemantics.lean#L13).

For the actual LEA+RET execution with a successful stack load, `addReturn_permission_iff` proves exactly:

```text
PermissionAll readable writable executable post actualEffects
  ↔ executable [start, start + size0)
    ∧ executable [start + size0, start + size0 + size1)
    ∧ readable initialRSP 8
    ∧ post exactFinalState
```

The write predicate disappears because this leaf emits no write request. There are exactly two execute requests and one scalar read in the interpreted effect computation. The execute ranges use the externally supplied Layout sizes, not decoded machine lengths. RET's target has not yet been fetched and therefore does not add a third execute request in this theorem.

`forbidden_stack_read_rejected` and `forbidden_exec_rejected` refute access to a denied stack range or first instruction range. `withinRegion` checks a full nonwrapping address span against an explicitly sized region. `seven_byte_stack_prefix_rejected` fails the actual eight-byte RET read under a seven-byte permission region, independently of successful map membership. `eight_byte_stack_region_positive` proves acceptance when both code ranges, the complete eight-byte stack region, the no-wrap premise, and the final postcondition hold.

This is a concrete producer/interpretation calculation for the chosen scalar leaf. It does not validate every Kraken producer, repair the previously observed AVX width mismatch, identify VM/Rust authority with this owned predicate, or prove that external layout sizes match physical instruction fetches. It does establish more than a source-only permission sketch for this actual program.

### The shared arithmetic observation has different machine interfaces

`result_is_wrapping_sum` checks that the X64 result's natural value is `(a + b) mod 2^64`. The AArch64 peer's full data theorem yields the same UInt64 sum in X0 and a return to X30's bits. The peer's closed proof was freshly rerun in a separate process to avoid the two models' overlapping root declaration names.

For s2n's inspected `BIGNUM_ADD_SUBROUTINE_CORRECT`, specialize the mathematical contract to one-limb input/output lengths `m = n = p = 1`, with suitable code/buffer/stack and aliasing premises. Its output limb in memory is `(a + b) mod 2^64`; its RAX result is the carry, not the wrapped sum. Thus the common output observation reads different locations:

| Route | Input representation | Sum observation | Return/resource mechanism | Evidence here |
|---|---|---|---|---|
| Kraken X64 leaf | UInt64 values in RDI/RSI | RAX | Eight-byte map cell at RSP; full modeled frame | Fresh universal body/return, permission, and rejection proofs |
| Kraken AArch64 peer | UInt64 values in X0/X1 | X0 | X30 link bits; full modeled frame | Preserved exact peer source freshly rechecked |
| s2n one-limb specialization | One-limb buffers plus six ABI arguments | Output buffer's limb | ABI-shaped stack/return and code/buffer premises; RAX carry | Exact upstream theorem inspection plus actual object/literal equality; no HOL replay |

The common mathematical observation is useful for selecting a pilot corpus. It does not establish operational replacement between these different interfaces, a cross-logic proof transport, exact trace equivalence, or a Rust-context theorem. The s2n source theorem uses its independent X64 model, but the present package does not prove a relation between that model's LEA/RET rules and Kraken's. [Selected s2n subroutine contract](https://github.com/awslabs/s2n-bignum/blob/4d1356a7470663c752660a59375dc3a9ef548428/x86/proofs/bignum_add.ml#L697).

The pilot inventory also reuses the frozen first-wave closure observations for X64/AArch64 XOR swaps and two-cell eight-byte store/load examples, plus X64 memory arithmetic. Their exact closure files are preserved under `support/reused/`; the named results have the same foundational trio. They prove the selected upstream register postconditions under their map premises, not the fresh leaf's stronger full frame. The s2n source theorem supplies the inspected carry relation, but no new Kraken carry theorem or HOL replay is claimed. `cases.json` keeps those evidence levels distinct instead of inventing new ports to fill a case matrix.

### The paired byte controls concern actual s2n object bytes

The preserved ELF object's SHA256 is `777578078e4239a142d2576fdb8ffb1dbe988d03711305092822e1d7cadf0797`. The defined `bignum_add` symbol contains 185 bytes with SHA256 `2ec605ad88338f62739324fed88147729e3a723be4197eb5480d07eee6153216`, exactly equal to the pinned `bignum_add_mc` literal list. The small unverified ELF importer was rerun in this package; it again rejects a one-byte code patch, changed ELF machine, and wrong symbol. Exact source/header/compiler/build records are preserved with the object. [Primary literal import](https://github.com/awslabs/s2n-bignum/blob/4d1356a7470663c752660a59375dc3a9ef548428/x86/proofs/bignum_add.ml#L15).

These controls and the actual Kraken footprint controls test distinct obligations. A byte patch changes the artifact; a hidden RBX write violates a frame; a denied stack byte violates an access contract; a wrong return target violates the exit condition. Passing one does not discharge the others. The X64 LEA+RET proof remains AST-plus-layout bound: it was not assembled or decoded in this package. The actual s2n object experiment does not silently bind those Kraken ASTs to bytes.

## Boundaries

- **Established:** a closed X64 full data/return-frame theorem with a generic decoded load and a UInt64 separation-cell witness; actual semantic wrong-return/clobber refutations; exact permission characterization with full-width positive/negative stack cases; rechecked AArch64 peer proofs and actual s2n object equality/byte controls.
- **Not examined:** a formal System V ABI witness, Rust source/import/caller/context bridge, canonical-address/fault relation, page permissions, or hardware execution. A named register interface and return theorem do not supply those missing premises.
- **Not examined:** Kraken-to-authoritative/reference ISA equivalence for even this leaf. The code computes the desired function in Kraken; the independent s2n result concerns another routine/model and does not close the per-instruction relation. AS04's detailed authoritative instruction investigation remains open.
- **Not examined:** generic Host embedding, fragment escape/overlap checking, PR-specific WP theorem closure, or a general `step1`/straightline bridge. The actual local composition proof advances the AS17 pilot but does not establish these broader mechanisms.
- **Not examined:** a matched complete pilot suite with multiplication, byte copy, pointer return, verified helper calls, and adequate scalar/SIMD comparisons, or controlled source/ABI/version repair measurements. Existing swap/memory/carry observations are retained with their actual theorem boundaries.
- **Not examined:** HOL Light replay, selected HOL imported assumptions, a chosen s2n access-safety theorem, or shared measured proof-production/repair costs across foundations. The one-sample Lean times include elaboration/import/checking and cannot be compared with an unrun HOL proof.
- **Known not to apply:** no mathematical equality or byte check here establishes contextual equivalence, constant-time security, relaxed-memory behavior, or a source-level Rust safety theorem. No first-wave package was changed.

## Evidence

`support/X64Pilot.lean` contains 18 semantic declarations plus the host-program identity. `support/AArch64Peer.lean`, its origin hash, and log preserve the exact peer source and two fresh checks. `support/results.json` records commands, source hashes, exits, closure counts, and one-sample wall times. Initial attempt logs distinguish ordinary failed elaborations from final successful evidence. Their public copies deterministically normalize private source prefixes, with raw/public hashes and the exact projection rule recorded; raw originals are excluded from publication. Final replay logs use relative source argv and portable recorded tool labels.

`support/s2n/` contains the new independent byte-check result and a manifest identifying the exact public companion inputs. The actual ELF object, literal bytes, importer, upstream assembly/header, compiler identity, and original build command remain in `../jasmin-vale-s2n-artifact-and-access-boundaries/support/`. Revalidation uses that published sibling package; no private cache or parent work directory is required. The original object assembly occurred in the first-wave experiment on 2026-10-14; this wave reran its byte comparison and controls without reassembly or execution.

`source-manifest.json` pins the underlying model and theorem source paths. `coverage.json` distinguishes these executed pilot results from unestablished stronger claims and genuinely unexamined research. All observations are dated 2026-10-14.

## Revalidation

Build the identified Kraken source with a chosen Lean version, then run `python3 support/run_pilot.py --lean /path/to/lean --kraken-lib /path/to/build/lib/lean`. The runner requires 18 X64 and two AArch64 semantic closure lists, each exactly the stated trio, plus one axiom-free host identity, and reruns the three s2n byte controls. It performs no installs, builds, network requests, native execution, or HOL replay. If packages are materialized separately, pass `--s2n-support /path/to/the/published/companion/support`.

After changing the X64 program, check the full frame, generic final-state iff, and permission iff together. A changed opcode may preserve the scalar sum while adding a clobber or memory access. After changing the architecture model or toolchain, recheck rather than assuming the printed closure persists. For an actual binary/ABI/Rust claim, add independently checked layout/decoder, caller, and resource witnesses; those arrows remain separate from the verified model computation.

*Authored by an AI agent acting on joshlf's behalf.*
