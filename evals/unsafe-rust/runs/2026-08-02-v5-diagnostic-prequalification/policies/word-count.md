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
binding. The raw report is sealed before counting. An over-cap report is a
canonical format defect, never grounds for retry or replacement. Integration
must freeze the counter source digest, passing self-test result, and per-mode
caps before launch. The content-bound receipt schema is
`word-count-receipt.schema.json`.
