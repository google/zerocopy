# Word-Count Policy — DRAFT / UNSEALED

Each target record supplies a positive integer `word_cap`; no cap is embedded
in this harness source. `word_count.py` version
`unicode-whitespace-runs-python-v1` decodes strict UTF-8 and counts maximal
Unicode non-whitespace runs with Python `str.split()`. Code blocks, headings,
tables, and citations count exactly like all other text.

The counter source, algorithm ID, and passing exact-byte integration binding are
covered by the prelaunch whole-file manifest and `STATIC-LOCK.json`.
Integration descriptor-captures the staged counter and the separately trusted
harness counter, requires exact byte equality, and compiles and executes only
the trusted capture. It rejects a staged-path change before accepting the
binding. The raw report is sealed before counting. An absent primary or bytes
that are not strict UTF-8 cannot be counted and produce the authenticated
terminal aggregation outcome `ERROR` at the report barrier. A present strict-
UTF-8 report is usable even when its canonical envelope records another format
defect. In particular, a spec-over-cap report retained below the frozen 4 MiB
capture ceiling is never grounds for retry, replacement, or premature
terminalization: Stage 01 records its exact count,
the remaining stages complete, and the final aggregate makes
`D-OUTPUT-VALID` fail. A report beyond that hard capture ceiling is
authenticated as unavailable and produces terminal `ERROR`; it is never
partially counted. Integration must freeze the counter source digest,
passing self-test result, and per-mode caps before launch. The content-bound
receipt schema is `word-count-receipt.schema.json`.
