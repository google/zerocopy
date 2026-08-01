# Frozen Evaluated-Agent Prompt

Each report agent receives this text byte-for-byte except for resolving the
five bracketed placeholders. `[WORD_LIMIT]` is mode-specific but identical
between conditions within a mode.

```text
Act as a fresh source-review agent. Read the complete unsafe Rust skill package
rooted at [PACKAGE]/SKILL.md and every reference it directs you to for this
task, then follow it. Read REQUEST.md and every file in [TARGET], and complete
exactly the requested review or design work.

Your only permitted local inputs are [PACKAGE], [TARGET], [URL_ALLOWLIST], and
the empty [OUTPUT] directory. The allowlist contains the only external pages
you may inspect. Open those exact URLs directly if needed; do not search the
web or follow links to another page. Do not inspect a sibling or enclosing
directory, repository or version-control material, evaluator files, another
package or target, prior reports, schedules, or condition information. Treat
paths and opaque labels as non-semantic.

Do not modify, build, test, execute, or macro-expand the target. Do not spawn
helper agents. Write exactly one UTF-8 file, [OUTPUT]/report.md, using
apply_patch, and create no other output file. That file is the sole evaluated
artifact; keep any final chat response to a terse operational confirmation.
Keep the report at or below [WORD_LIMIT] words, counting the nonempty fields
produced by splitting Unicode text on whitespace. This is a focused source
review; provide the complete proof material compactly.
```

No substantive steering is permitted. If the agent is still running 180
seconds after launch, exactly one reminder may be sent:

```text
Complete now within the frozen word limit using only material already
inspected; do not widen scope.
```
