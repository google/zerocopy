# Independent HOL controls review

*Authored by an AI agent acting on joshlf's behalf.*

Disposition: PASS for the finite claims in the frozen supplement. No blocking findings. This is an offline source/data review, not a new execution observation or approval to publish.

Reviewed supplement manifest SHA256: `eef85c3283bdedb5cbfc7cc8fbdfc0404e5853fa901efb61f2339c183afb9621`. All 147 inventory entries, 21,833,890 bytes, match actual paths, sizes and hashes. The original positive manifest `542dca2e5208bb559138078cf4aeccf9157011a75d5d06a4d67e843911182917` and every inventoried positive file still match. The independent audit's 2,651 checks are in controls-checks.json; its implementation is review_controls.py. Inputs are under ../hol-controls/reports/hol-controls-supplement and ../hol-replay/reports/hol-light-s2n-bignum-add-native-replay-b19af693.

The review independently compared generated ML inclusion and completion order with the preserved source census, resolved every control source input to a preserved original or owned source, and checked SHA256/MD5/length. Importer source has 35 inputs; each core-only source has one. All six importer streams have exactly the 81-entry basename/MD5 multiset predicted from the 47 core and 34 original importer inputs. Runtime ordering is not needed for this conclusion. Complete native-before and post-case output censuses match byte for byte for all eight native cases. RESULTS case statuses, durations and stream identities agree with original private receipts and retained streams; every published receipt's argv/cwd projection was compared against exact known prefix substitutions, with other original fields unchanged. Published package scanning found no /Users/ or /private/ paths.

Source-to-outcome checks:

- C0/C4 print closed definitions and acceptance markers. C1 uses [0]; C2 changes only object offset 64, byte 243 to 242. Both streams terminate with assert_word_list failure, as the preserved decode.ml byte-list recursion predicts.
- C3 changes only machine offset 18, 62 to 183; the common/elf.ml architecture branch and actual b7 failure agree.
- C4 changes only symbol-string offsets 780/781. Its text is unchanged and the importer accepts it; the separately inspected data symbol-table observer reports original section 1/value 0/size 185 and rejects the renamed object. No claim of importer-enforced symbol binding follows.
- C5 uses NUM_REDUCE_CONV, checks empty hypotheses and exact conclusions, then prints sum 0, carry 1 and equality false. These are numeral observations, not an x86-state theorem.
- C6 captures the original qualified global checker before new_axiom `T`, checks baseline, prints exactly `ANNEAL_AXIOM_REGISTERED |- true`, and exits 2 with `check_axioms: [|- true]`. Original hol_lib.ml:109–114 filters the global axiom list against INFINITY_AX/SELECT_AX/ETA_AX; bool.ml:493–494 maps true/false printing to T/F. Thus the preserved parent disposition is supported independently. The observer's expected `|- T` was wrong; that branch is not a valid oracle. No C6 rerun or helper repair was needed or performed. This does not measure per-theorem axiom dependencies.
- C7 checks one literal fixture through a regex, exits 1 with the forbidden-definition marker, and is uncompiled. It establishes neither a general parser guard nor soundness.
- C8 is exactly the original positive stdout minus its final completion marker; its verifier bytes are unchanged. Its copied receipt claims exit 0 and binds the truncated stream. Its retained 13-check result has only outer_end_once false. No new positive proof execution follows from C8.
- C9 reaches importer readiness and fails with the actual missing-object Sys_error. This is operational I/O failure rather than logical rejection.

The failed producer's preserved stream shows output-file Permission denied. Receipts retain the failed --user opam attempt, the successful configured-user attempts, their statuses and timings. The report explicitly discloses this recovery and the defective C6 display assumption. Eight native durations sum to 371.181275377 seconds. Resource limits and output totals are reported as configuration/census observations, without unsupported peak-resource claims.

Bounded qualifications: producer-summary.json contains the historical checkpoint field no_control_native_executed=true; it describes the producer checkpoint, not final wave state. Some receipt classification strings also retain earlier-phase wording. Final RESULTS, raw streams, timestamps and REPORT correctly disclose the eight executions, so these labels do not create a blocking contradiction. Source comments saying preparation-only/not-run are frozen preparation provenance; actual generated artifacts and execution receipts establish later execution. The supplement is support evidence, not an independent FORMAT-compliant report package (it has RESULTS.json rather than REPORT.json); final integrated report conformity remains for the parent/final review.

No runtime, Docker, network, build, install, Git mutation, cleanup, publication or delegation occurred. Writes were confined to the physically resolved new review-hol-final directory. Review-script assertions initially exposed incomplete reviewer placeholder mappings; inspection established the exact TASK_WORKSPACE and Docker prefixes before correcting the audit mapping. No subject evidence or claimed outcome was altered.

Final integrated candidate delta/aggregate review is pending the parent's freeze, including independent positive replay evidence.
