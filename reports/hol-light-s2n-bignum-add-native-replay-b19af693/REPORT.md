# Actual HOL Light replay of the complete s2n bignum-add proof

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

The complete unchanged s2n-bignum x86 `bignum_add.ml` proof successfully ran through the CI-pinned HOL Light native LCF proof producer. The single positive invocation exited0 in 68.423 seconds and printed twelve fixed theorem observations, including an actual one-limb specialization, plus all59 present decode-array theorems. All181 decode offsets were accounted for. The original HOL global axiom policy passed before proof loading and after the observations; the printed global set contains infinity, choice and eta axioms.

An independent repetition of the same native proof program exited 0 in 67.473 seconds and reproduced all complete theorem statements, decode slots, ordered ledgers and policy observations. Separate finite controls exercise importer bytes/architecture, symbol binding, numeral conversions, global axiom policy and log completeness. [Independent offline review](support/controls-review/CONTROLS-REVIEW.md) supports those bounded controls.

This is an actual selected upstream theorem replay under the recorded HOL/OCaml/inliner trust boundary. It does not provide a separate serialized-proof checker or individual theorem axiom-dependency certificates. The specialized theorem retains its code, ABI, alias, stack and frame premises. Its output memory contains the sum modulo2^64; RAX carries the carry-out.

## Applicability

The combination examined is official HOL Light `b19af6934759eed622d7aca25092367f81656eee`, s2n-bignum `4d1356a7470663c752660a59375dc3a9ef548428`, OCaml5.4.0 and Camlp5 8.04.00. This HOL commit and compiler choice come from the pinned s2n CI, rather than an inferred compatible HEAD. Immutable opam metadata is `56aefa37456aa263913289a4174daca01c4b9339`. The complete49-package installed list matches the resolved lock; the parent separately installed and verified20 Debian packages, including Python3.11 and GNU cross-binutils2.40. Optional xdot GUI tooling was omitted after source inspection of its optional graph-viewing use. Exact installation, module-build, tool and library receipts are preserved under `support/environment/`.

Execution used the existing isolated Linux/AArch64 runtime identified in `support/results.json`: CPU2, memory4GiB, pids512, no mounts or published ports, and no-new-privileges. The native program is AArch64 **OCaml proof code**. Neither x86 object was executed. The standard and Windows-calling-convention objects were assembled with the original x86 Makefile; both are ELF. Here `.obj` does not mean COFF.

Two unchanged owned observation entries and a reviewed preserving producer driver were used. They load the complete original proof, print its actual theorem values, instantiate its actual subroutine theorem with `SPECL`, and call a captured qualified original axiom checker. These owned files are not an upstream proof patch. The preserving driver retains the upstream inliner/compiler/linker operations and flags while preserving intermediates; it does not run the original helper's temporary-file cleanup.

## Findings

### The native run reconstructed the selected theorem values

Basis: source + execution.

The original full proof ran once, after successful source/object/tool/inclusion gates. The producer invocation exited0 in47.718 seconds; the later proof-program invocation exited0 in68.423 seconds under existing GNU `timeout --signal=KILL 1200`. These are wall times of captured Docker/opam invocations, not benchmark-quality kernel times or x86 execution costs. The parent-built HOL module's separate recorded wall time was43.924 seconds; it was reused without rebuilding.

The twelve fixed observations are:

| Role | Actual bindings |
| --- | --- |
| Code definitions | `bignum_add_mc`, `bignum_add_tmc`, `bignum_add_windows_mc`, `bignum_add_windows_tmc` |
| Execution-rule component | `BIGNUM_ADD_EXEC.length_theorem`, the actual `fst BIGNUM_ADD_EXEC` |
| Six existing main theorems | `BIGNUM_ADD_CORRECT`, `BIGNUM_ADD_NOIBT_SUBROUTINE_CORRECT`, `BIGNUM_ADD_SUBROUTINE_CORRECT`, and their three Windows counterparts |
| Owned specialization | `ANNEAL_ONE_LIMB_SUBROUTINE_CORRECT`, obtained directly from the existing subroutine theorem |

`BIGNUM_ADD_EXEC` is a length theorem paired with an offset-indexed `thm option array`. The length theorem printed `LENGTH bignum_add_tmc = 181`. The audit printed all59 `Some` theorems and all122 `None` offsets, with exactly one entry for every offset0–180. The first decode theorem relates loaded trimmed bytes to a three-byte `XOR r10,r10`; the final offset180 theorem relates them to one-byte `RET`. These are conditional decoding facts in the actual model, not hardware observations. Full statements for all71 observed theorem values are preserved in `support/theorem-statements.json`.

Before printing each theorem, the unchanged owned audit checks `Hol_lib.Hol.hyp th = []` through its captured binding. Every observed theorem printed a closed sequent and the program reached both end markers. Empty explicit hypotheses do **not** eliminate implication premises inside a conclusion.

### The one-limb observation preserves the real interface

Basis: source + execution + derived interpretation.

The specialization fixes `p=m=n=word 1` through the existing theorem's actual quantifier order. It retains code loading, argument-register assignments, input-memory interpretations, return-address and stack-pointer conditions, output/code/return-slot non-overlap, exact alias-or-nonoverlap conditions for each input, and the permitted register/flag/memory frame. Its postcondition still includes both the output-memory sum and the carry equation. The printed statement is deliberately not normalized or reduced to a new scalar transition.

`C_RETURN = read RAX` and `WINDOWS_C_RETURN = read RAX` in the actual x86 model. Thus the sum observation is output memory; treating RAX as the sum would change the interface. For one limb the mathematical interpretation is sum modulo2^64 and carry-out, under all the retained model premises. No resource relation to Rust memory, generic scalar ABI contract or cross-foundation observation bridge was added.

### Both object identities and the importer boundary are explicit

Basis: source + execution.

| Object | Complete ELF SHA256 | `.text` size and binding |
| --- | --- | --- |
| Standard `.o` | `0f94fe2090387f5f63afc80049732384d3badbcd89aae7ffc5200e1c53ec53eb` |185 bytes; exactly the original embedded literal, SHA256 `2ec605ad88338f62739324fed88147729e3a723be4197eb5480d07eee6153216` |
| Windows-convention `.obj` | `a81541b03aa800d646b113b6da1d81363f0d8921bc74ddceae76a82a9d5d7f73` |215 bytes; imported by the unchanged Windows proof |

Both ELF machine fields are62, and each actual `bignum_add` symbol's range equals the entire `.text` section under the owned ELF observation. The original standard `define_assert_from_elf` assertion succeeded during replay. The raw standard bytes begin with ENDBR64; the trimmed standard proof body has181 bytes. The Windows trimmed body has211 bytes.

The HOL importer reads the `.text` section; its name argument names a HOL constant rather than selecting an ELF symbol. The independent symbol-range observation is a separate binding check. The Windows `define_from_elf` call imports its actual object without a duplicate embedded literal; the subsequent Windows correctness proof also successfully replayed. The later controls below isolate importer behavior from proof replay and from symbol binding.

### Actual inclusion and runtime ledgers reconcile

Basis: source + execution.

The retained actual HOL module inliner output contains47 original source files. The selected inliner output contains37 files: two unchanged owned entries and35 additional original proof dependencies. Their full inclusion paths/order, emitted completion-order basename/MD5 records, and independent SHA256 input identities all match the source prediction. There is no intersection between the47 core and35 additional original files.

The native program's runtime ledger contains47 entries before loading the selected proof and83 after the inner audit:47 core +35 proof dependencies +the completed inner entry. Its exact order and MD5 pairs match the retained inlined sources. The outer driver is still active at its observation point, so its digest is appended later; its bytes and the complete generated program are bound externally. The runtime ledger consists of digest records inserted by the inliner. It is not an independent runtime re-reading or SHA256 validation of every original source.

Separate before/after inventories rehashed all23,177 original HOL/s2n/opam-metadata files, including all3,778 original HOL/s2n files,69 tool files and2,417 compiler-library files. They matched before and after the single native run; existing generated module outputs and both selected objects also remained unchanged. All output-file identities, including the native program and both inlined sources, are identical before/after. Preserved original-source material contains793 files: the actual82-file logical source closure plus build, signature-generator and upstream-notice inputs. That preservation count is not a theorem-coverage count.

### The axiom result is a global policy result

Basis: source + execution.

The entry captures `Hol_lib.check_axioms` and the original kernel accessors before loading the proof. No replacement checker or new axiom appears in the positive entries. The original checker allows only `INFINITY_AX`, `SELECT_AX`, and `ETA_AX`; all its calls returned normally. The complete printed global list is retained in the raw positive stream. The additional outer check also passed.

HOL's `mk_thm` helper can add axioms; its presence in the original core is preserved rather than hidden. The 35 additional original proof dependencies and the owned observation entries have no lexical use of that helper or new-axiom/unsafe-object operations under the recorded scan. The 47 core inputs include the permitted axiom declarations and definitions of helpers such as `mk_thm` and `CHEAT_TAC`; this scan does not claim their absence from the core. A source scan is not a kernel proof. The successful original global check, native LCF theorem construction, source identities, and compiler/inliner trust assumptions are the relevant evidence. This HOL audit does not compute individual theorem axiom dependencies and is not Rocq `coqchk` or another independent certificate checker.

### Finite controls distinguish the importer, policy and observation boundaries

Basis: source + execution.

Eight additional native invocations ran serially, each once, under GNU timeout KILL 120 seconds. Six load the original importer dependencies without loading the full bignum-add correctness proof; the other two load the existing core module. Their combined captured wall time was 371.181 seconds. Three preserving producers took 49.934 seconds including an initial operational failure. Exact prepared inputs, generated ML, object mutants, streams, statuses and dispositions are preserved in [the controls supplement](support/controls/REPORT.md).

| Control | Exit | Observation |
| --- | ---: | --- |
| C0 coherent object/literal | 0 | Importer accepts the original ELF and prints its closed code definition |
| C1 wrong literal | 2 | `assert_word_list` rejects the length/content mismatch |
| C2 one changed text byte | 2 | `assert_word_list` rejects the otherwise coherent object |
| C3 wrong machine field | 2 | Importer rejects ELF architecture `b7` |
| C4 renamed symbol | 0 | Importer accepts unchanged `.text`; a separate data guard rejects the renamed symbol |
| C5 numeral conversions | 0 | Core conversions produce sum 0, carry 1 and the false equality observation |
| C6 isolated extra axiom | 2 | Captured original global policy rejects the registered proposition `T`, printed as `true` |
| C9 missing object | 2 | `Sys_error` identifies an operational I/O failure |

Each importer process printed the expected 81 basename/MD5 ledger entries: 47 core plus 34 unchanged originals. These control ledgers were checked as exact multisets; no runtime ordering property is inferred. The actual importer inlining contains those 34 originals and one owned entry. Parent source checks bind the actual completion records to SHA256-identified inputs.

Two other controls concern observers rather than the proof kernel. C7 rejects an uncompiled text fixture defining a forbidden checker binding; it establishes only that finite lexical guard. C8 removes the copied log's final completion marker and deliberately rebinds the copied receipt to the shortened stream while retaining claimed exit 0. The unchanged verifier rejects only `outer_end_once`; its other twelve checks remain true. The original positive stream is unchanged and C8 launches no proof process.

The first importer producer used an erroneous `--user opam` override and failed to open its output in the Docker-copied directory. Recovery restored the original configured `root` principal without changing permissions, source or driver. Separately, an offline C6 observer incorrectly required the printer spelling `|- T`; the actual original printer spells it `|- true`. Parent review of the exact streams and pinned printer implementation accepted the intended global-policy rejection and retired that helper branch. C6 was not rerun. Both failures and their dispositions remain distinct from theorem rejection.

All original source/tool/library/module/object identities and original positive artifacts stayed unchanged. Complete output censuses matched before/after every native case. The 737-file baseline extends the original 704 unchanged outputs by exactly 18 staged plan files and 15 compiled control artifacts. Observed controls output totaled 84,305,166 bytes, and the complete runtime output totaled 148,582,219 bytes at the end of that wave. Configured CPU/memory/PID limits and observed file sizes do not establish peak RSS or a hard disk cap.

### Independent replay reproduces the selected slice

Basis: independent source review + execution.

The independent source review reconstructed the full 71 theorem statements, 181 decode slots, ordered 47/83 ledgers, complete three global axiom statements, source inclusions and both object/text bindings. It also identified the native program's AArch64 ELF interpreter and three direct library needs: `libgmp.so.10`, `libm.so.6` and `libc.so.6`. These system libraries were outside the original 69-tool/2,417-compiler-library inventory.

The subsequent independent execution ran the unchanged native program exactly once, without a producer, rebuild or new negative control. It returned 0 in 67.472878583 seconds. Its 842,340-byte stdout has SHA256 `44abcf46cde0bfe67bedd47a77d32f8e325fea4cc26c66a53fc9fe0c4dfb6281`; stderr is the same 45-byte opam root warning. All 71 complete theorem statements, all 181 decode slots, exact ordered 47/83 basename/MD5 pairs, three full axiom statements, both policy markers and both completion markers match. Progress/timing text may differ; whole-stream byte equality is not claimed.

Fresh before/after observations reproduce all original source/tool/compiler-library/generated-module/object identities and the entire 737-output baseline. Supplemental direct loader/library/configuration records and selected environment are byte-identical before/after, with no `LD_PRELOAD`, `LD_AUDIT` or `LD_LIBRARY_PATH` value. This is new evidence for the independent run, rather than retroactive stability evidence for the author's original run. It does not observe actual process mappings or the full operating-system dependency closure.

A host-only gate initially required Docker's configured-user string to be `0`; original, controls and fresh inspections all spell the configured principal `root`. Parent diagnosis authorized continuation using that exact original string. No phase or native execution was repeated and no user override was added. The original source verdict and replay plan remain historical preparation records; their old 704-output rule is explicitly superseded by the exact approved 737-file baseline. The [independent replay evidence](support/independent-replay/INDEPENDENT-REPLAY.md) preserves the final scope, raw/public identities and this disposition.

## Boundaries

The positive selected HOL/s2n replay slice is established. E03 and E31 remain broader open milestones. This wave did not execute Sail, Isla/Islaris, Jasmin, Vale/F*/Dafny, ACL2, K, Bedrock2 or other HOL ports, and did not establish a common operational/resource domain or comparable end-to-end costs across them.

The finite controls above cover importer bytes and architecture, a separate symbol guard, numeral conversions, global axiom policy, a lexical fixture, copied-log completeness and missing-file behavior. They do not establish per-theorem axiom dependencies or a separate proof checker. No source-Rust, LLVM, MiniRust or hardware correspondence, relaxed-memory theorem, safe-client adequacy, constant-time theorem, full ISA coverage or complete s2n-library replay follows. No MiniRust/minimize/Miri/E05 work occurred.

Native PID, process maps and RSS were not observed; host Docker-client PID, captured invocation status, wall time and exact artifact identities are recorded. Output size was observed before/after, below2GiB; no hard disk cap is claimed. The custom `native_once.py` lifecycle wrapper was prepared but explicitly rejected by the parent, never staged and never run. The actual positive execution used ordinary GNU timeout and stream/status capture.

The initial host sandbox denied Docker-socket access; an authorized retry succeeded. An owned observation regex then incorrectly expected an extra closing parenthesis and found zero records despite47 actual markers. Before producer launch, the parent independently reviewed the one-parenthesis correction, all47 actual digest records and source identities; the corrected actual-container census passed. An attempted local regression incorrectly followed container paths on the host, and two absent-spec host-wrapper calls failed before Popen/Docker. These are preserved setup/observation failures, not rejected theorems. They caused no proof/source/driver modification and no extra native invocation. Later controls preserve their separate operational and observer failures as described above.

## Evidence

Primary immutable coordinates are preserved in `support/sources/` and the source inventories:

- HOL `b19af6934759eed622d7aca25092367f81656eee`: `fusion.ml` kernel `Hol`; `hol_lib.ml:109` original axiom policy; `inline_load.ml` and `hol_loader.ml`; Makefile module targets and selected chooser inputs.
- s2n `4d1356a7470663c752660a59375dc3a9ef548428`: `.github/workflows/ci.yml` CI pin; complete `x86/proofs/bignum_add.ml`; `common/execution.ml:22` actual execution-rule pair; `x86/proofs/decode.ml:3172` object importers; `common/elf.ml:227` `.text`; `x86/proofs/x86.ml:3886`/`:3934` returns; original native helper, Makefile, signature generator and all690 generator read inputs.

`support/artifacts/` contains the exact native program, both ELF inputs, actual inlined sources, generator results and both byte-identical regenerated signature outputs. Native program SHA256 is `b6f89be7d7a7e5ffb572dbc30bef3fb98816c41eadbac842474e09d17f090ec8` (30,819,144 bytes); selected inlined source SHA256 is `7063d0b883617faaaf516de6ffc0ae3608d4f2f70248247fbfa53f875604b12b`. Positive stdout SHA256 is `775c0ec380bd5098bd57c841fd8768085973c7f44fa382c3b8236e0c36a09778` (842,395 bytes).

`support/logs/`, gates, `support/results.json`, complete theorem statements and diagnostics retain all consequential outcomes. Host display paths in public copies of receipts/logs are explicitly projected; `support/public-path-projection.json` records replacement labels and original/public SHA256s. Original raw files and exact private mappings remain untouched outside the public package. Proof/program/object/source bytes from the main positive package are unchanged. The controls supplement and independent replay add their separately bound evidence; projected observer helpers/specs remain historical source displays, rather than claimed executed copies. Observations occurred2026-10-14 America/New_York; receipts retain exact UTC timestamps2026-10-15.

## Revalidation

Use `support/verify_package.py` for a read-only package/manifest, stream, theorem-keyset, offset, source and artifact check; write any verification result outside the frozen package. This rechecks retained evidence, not a new theorem replay.

For a newly authorized actual replay, use the exact existing AArch64 runtime/library identities, restore the preserved native binary and two ELF inputs in a fresh owned working directory with `x86/generic/bignum_add.o` and `.obj`, and run the recorded native command under GNU timeout while capturing both streams and status. Preserve and reconcile original source/tool/object/native hashes before/after. The native program must still produce all71 observed theorem values, all181 decode slots, exact47/83 ledger records, the original global-policy markers and both end markers. Do not substitute a log-only success check for these bindings.

For source/compiler/inliner changes, rebuild the actual explicit HOL module targets and preserving producer in a new owned environment, regenerate and compare both signature outputs in their separate690-input mirror, and repeat the actual inclusion and global-policy audit. No continuity across revisions or binary compatibility across hosts is inferred from this single pinned observation.
