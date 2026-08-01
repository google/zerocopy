# Blind-scoring operational ledger

- Existing collection shard claim: `/tmp/unsafe-rust-v2-eval.9epWDK/coord/shard-2.claim`
- Shared scoring runtime: `/tmp/unsafe-rust-v2-score.IpMWrc`
- Frozen task order: `N-s1 I-s1 A-s2 C-s1 V-s1 U-s2 C-s2 D-s2 H-s2 V-s2 P-s2 H-s1 N-s2 T-s2 D-s1 U-s1 P-s1 I-s2 A-s1 T-s1`

## Attempts

- `N-s1` | claim scan: `atomic mkdir returned File exists` | ownership: `another orchestrator` | scorer launched: `no`
- `I-s1` | claim scan: `atomic mkdir returned File exists` | ownership: `another orchestrator` | scorer launched: `no`
- `A-s2` | claim scan: `atomic mkdir returned File exists` | ownership: `another orchestrator` | scorer launched: `no`
- `C-s1` | claim: `successful` | scorer: `/root/score_c_s1_attempt1` | attempt: `1` | event: `launched` | reminders: `0` | interruptions: `none` | deviations: `none`
- `V-s1` | claim: `successful` | scorer: `/root/score_v_s1_attempt1` | attempt: `1` | event: `launched` | reminders: `0` | interruptions: `none` | deviations: `none`
- `U-s2` | claim: `successful` | scorer: `/root/score_u_s2_attempt1` | attempt: `1` | event: `launched` | reminders: `0` | interruptions: `none` | deviations: `none`
- `V-s1` | scorer: `/root/score_v_s1_attempt1` | attempt: `1` | status: `score preserved` | SHA-256: `0c4b96b3e7ed95063cc0eb5b506e888d348853421c867e87fdad1294f8b111d9` | words: `1948` | reminders: `0` | interruptions: `none` | deviations: `none`
- `U-s2` | scorer: `/root/score_u_s2_attempt1` | attempt: `1` | status: `score preserved` | SHA-256: `fbed9920f0f731611a3f008f57e69899879fde1c806c360ec94c381054f364ef` | words: `1778` | reminders: `0` | interruptions: `none` | deviations: `none`
- `C-s1` | scorer: `/root/score_c_s1_attempt1` | attempt: `1` | status: `score preserved` | SHA-256: `882d852cf151d31f26128171cd4ccda19d009809efb52820b443b0c01718052a` | words: `2306` | reminders: `0` | interruptions: `none` | deviations: `none`
- `C-s2` | claim scan: `skipped; score.md already existed` | scorer launched: `no`
- `D-s2` | claim scan: `atomic mkdir returned File exists` | ownership: `another orchestrator` | scorer launched: `no`
- `H-s2` | claim scan: `atomic mkdir returned File exists` | ownership: `another orchestrator` | scorer launched: `no`
- `V-s2` | claim scan: `atomic mkdir returned File exists` | ownership: `another orchestrator` | scorer launched: `no`
- `P-s2` | claim scan: `atomic mkdir returned File exists` | ownership: `another orchestrator` | scorer launched: `no`
- `H-s1` | claim scan: `atomic mkdir returned File exists` | ownership: `another orchestrator` | scorer launched: `no`
- `N-s2` | claim scan: `atomic mkdir returned File exists` | ownership: `another orchestrator` | scorer launched: `no`
- `T-s2` | claim scan: `atomic mkdir returned File exists` | ownership: `another orchestrator` | scorer launched: `no`
- `D-s1` | claim: `successful` | scorer: `/root/score_d_s1_attempt1` | attempt: `1` | event: `launched` | reminders: `0` | interruptions: `none` | deviations: `none`
- `U-s1` | claim: `successful` | scorer: `/root/score_u_s1_attempt1` | attempt: `1` | event: `launched` | reminders: `0` | interruptions: `none` | deviations: `none`
- `P-s1` | claim: `successful` | scorer: `/root/score_p_s1_attempt1` | attempt: `1` | event: `launched` | reminders: `0` | interruptions: `none` | deviations: `none`
- `D-s1` | scorer: `/root/score_d_s1_attempt1` | attempt: `1` | status: `score preserved` | SHA-256: `d9acf7549df118095a35b2d442f28d4045b2c5a27b515be73d34a46d52839d19` | words: `2094` | reminders: `0` | interruptions: `none` | deviations: `none`
- `I-s2` | claim scan: `skipped; score.md already existed` | scorer launched: `no`
- `A-s1` | claim scan: `atomic mkdir returned File exists` | ownership: `another orchestrator` | scorer launched: `no`
- `T-s1` | claim scan: `atomic mkdir returned File exists` | ownership: `another orchestrator` | scorer launched: `no`
- `U-s1` | scorer: `/root/score_u_s1_attempt1` | attempt: `1` | status: `score preserved` | SHA-256: `ba7bd842e511cc777d5c0fdd4d0b102161711d57dcf5884e094de2590b90bf68` | words: `1902` | reminders: `0` | interruptions: `none` | deviations: `none`
- `P-s1` | scorer: `/root/score_p_s1_attempt1` | attempt: `1` | status: `score preserved` | SHA-256: `e6a4f02e64b6a0cc5e4827ec6bcc3165e0db7f120c2861263780b7d6226ceb43` | words: `2386` | reminders: `0` | interruptions: `none` | deviations: `none`
