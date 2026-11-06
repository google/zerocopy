# Fixed byte-law certificate completion

The independently fixed roots are the exact four whole-law SMT files in the
earlier matched-candidate experiment, hash-bound in its predicate-map.json.
The five false-law roots and narrowed-domain root are retained unchanged.
No root assertion, domain, goal conjunct or metadata flag may change.

cvc5 emits a result and its raw Alethe export. A separate untrusted bounded
producer may reconstruct derivations from the exact input root. Only unchanged
native Carcara, with that exact root file, determines certificate acceptance:
exit code zero AND stdout exactly `valid\n`. `holey` is rejection even with
exit zero. Neither cvc5 UNSAT nor the producer's own report is acceptance.
The producer emits only native checker rules; no custom rules or allow lists.

All subprocess stdout/stderr and statuses are captured separately. Timeouts and
operational failures remain distinct from invalid certificates. Unexpected
panic/assertion stops dependent work pending root-cause and blast-radius review.
Writes, copied owned fixtures and logs stay in this execution directory; original
scratch, published corpus, tools, sources and Git state stay read-only.

Root bytes/hashes are revalidated at consumption. A certificate tied to another
domain, weakened claim, omitted initialization, aliasing frame, value 2, missing
stability or omitted array index must not be accepted for the corresponding full
consumer root. The unchanged Rust/source correspondence frontier is a premise,
not discharged by successful SMT checking.
