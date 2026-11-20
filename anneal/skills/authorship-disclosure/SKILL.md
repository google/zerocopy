---
name: authorship-disclosure
description: >-
  Maintain accurate, nonredundant AI-authorship disclosures when preparing
  externally visible prose or Git commits, including revisions and handoffs.
---

# Authorship disclosure

Disclose material agent contributions that remain in the work, not its drafting
history. Ordinary conversation with the user and private scratch work need no
notice. Include required notices in publication-ready handoffs. Use the Git rule
for a commit's files and message; use the prose rule for separately presented text.

## Judge and maintain the final work

A contribution is material when significant agent choices remain in wording,
selection, organization, argument, tone, implementation, or meaning. Size alone
does not decide materiality. Mechanical copying, formatting, or committing adds
no authorship; substantive editing or conflict resolution can. Adding or updating
this skill's fixed disclosure boilerplate is mechanical, not message authorship.

Count retained contributions from earlier turns and delegated or predecessor
agents. Human retyping, approval, and mechanical transformations do not erase
them; generated output can retain agent-designed content.

Within your authorized editing scope, update or consolidate disclosures in place;
remove notices that no longer apply, including for discarded contributions.
Earlier turns and authorized handoffs do not freeze notices or require new ones.
Removing words does not remove authorship if their substance remains elsewhere.
Preserve distinct attribution and applicable disclosures for retained third-party
work. Do not relabel work done on someone else's behalf as your user's, alter
unrelated notices, or infer human authorship from a missing disclosure.

In notices you create or revise under this skill, `AI agent` is literal wording,
not a placeholder for ChatGPT, Codex, a model, vendor, or individual agent name;
replace only the angle-bracketed fields below. For `<user>`, use an audience-appropriate
identifier the user has established or authorized for that context. Do not infer permission
to reveal a legal or more identifying name; if none is suitable, resolve one before committing
or publishing the notice. This does not require renaming inherited third-party attribution.

## Prose

For an independently presented item that could appear to be the user's, disclose
material agent authorship with one visible, accurately scoped notice:

`<Verb> by an AI agent acting on <user>'s behalf.`

Use an accurate verb, such as `Authored`, `Updated`, or `Partly authored`. Italicize
in Markdown. Prefer one accurately scoped notice over separate labels for interleaved passages.

This skill requires no prose notice when a visibly distinct AI/bot identity reaches the
intended audience, or the user explicitly adopts the identified prose or a clearly scoped
class as their own. Review or permission to publish is not adoption; apply it only within its scope and reevaluate later material edits.

## Git commits

For new agent work, use the user's established Git name and email for the
contribution context. Resolve missing or conflicting identity; do not invent an
address, use another person's identity, create an agent Git author, or add an
agent `Co-authored-by`. Preserve other contributors' attribution when carrying
forward their work.

Treat a commit's content and message as one disclosure unit. Content means the
recorded diff, including deletions, not the message or unchanged parent content.
For retained material agent contributions made on this user's behalf, select
exactly one row and maintain at most one trailer in the final trailer block:

`Agent-authored-by: AI agent acting on <user>'s behalf`

| Agent contribution to content | Agent contribution to message | Trailer suffix |
| --- | --- | --- |
| Yes | Yes | No suffix |
| Yes | No | ` (content only)` |
| No | Yes | ` (commit message only)` |
| No | No | Omit trailer |

The qualifiers are alternatives, not additional trailers. Recompute the row when
amending, rebasing, or squashing; consolidate redundant same-user notices. Apply
the table separately to each represented user. For example, writing a message for a
content-only change replaces that qualifier with one unqualified trailer. Preserve
distinct third-party provenance separately.
An older unqualified trailer does not establish message authorship. If available
provenance leaves material uncertainty, leave it unchanged and report the limit.

The trailer records material participation in the indicated parts, not sole
authorship or human review. Prose adoption and bot identities do not replace Git
provenance. Use the trailer, not extra notices in the message or each file. PR
descriptions, review comments, and separately published documents use the prose rule.

## Publication

Ensure required notices survive the actual rendering and publication path.
Inspect publication results you control when available; report unverified results
as unverified. Report discovered disclosure loss and repair it only within your
authority. If the path cannot preserve required attribution or disclosure, keep
the candidate unpublished and explain the limitation.

This skill does not authorize publication, history rewrites, or certifications
such as `Signed-off-by`, and does not waive independent disclosure requirements.
