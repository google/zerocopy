# Local/nested definition probe

Not executed during the 2026-09-24 investigation.

```console
rustc +nightly-2026-05-31 -Zunpretty=hir-tree local.rs > hir-tree.txt
```

For exact identity results, use a `rustc_driver` probe to enumerate local DefIds
and print DefKind, DefPath, DefPathHash, parent and span.

Then insert an additional closure and inline const before the marked ones and
compare anonymous DefPathHash changes.
