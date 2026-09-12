# Copyright 2026 The Fuchsia Authors
# SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
"""Apply scoped follow-ups to pinned commits and publish only new staging refs."""
import base64
import hashlib
import json
import os
from pathlib import Path

from prepare import REPO, api, git

GROUPS = {
    3675: (
        "joshlf/audit-core-fixes-20260912",
        "a8c424d5f38d9794ce51277c9bc96fafaf89d88c",
        "joshlf/audit-core-fixes-20260912",
        "a8c424d5f38d9794ce51277c9bc96fafaf89d88c",
        "Cite the field-placement rule for `Unalign`",
        "The alignment-modifier rule does not establish the first field's\noffset. Cite the Rust 1.56 repr(C) layout algorithm, which starts at\nzero and places the first field after rounding that offset for alignment.\nThis changes only the proof, not the implementation.",
    ),
    3676: (
        "joshlf/audit-macro-fixes-20260912",
        "8b67e0f626b141c2659a86fd6ae659d7a8c842a4",
        "joshlf/audit-macro-fixes-20260912",
        "8b67e0f626b141c2659a86fd6ae659d7a8c842a4",
        "Test source recovery after failed transmutation",
        "Add a runnable byte-to-bool example that recovers the original source\nfrom ValidityError. Use concrete types with the required trait impls,\nand check the documented failure outcome without ignoring the result.",
    ),
    3677: (
        "joshlf/audit-pointer-contracts-20260912",
        "846c7e2c02e359f782ff82667de350bf63949a93",
        "joshlf/audit-recovered-3677-34723108904",
        "6f6772fdb950925aed4972986f08b7272a9dafc4",
        "Align pointer proofs with their local contracts",
        "Justify projection's allocation and provenance obligations directly\nfrom Project rather than the preceding non-nullness proof. State the\nwith_meta proof in terms of the constructed raw pointer and the caller's\nobligations for its resulting referent.",
    ),
}


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise RuntimeError("Expected exactly one occurrence of: " + repr(old[:100]))
    return text.replace(old, new, 1)


def edit(pr, worktree):
    if pr == 3675:
        relative = "zerocopy/src/wrappers.rs"
        path = worktree / relative
        text = path.read_text()
        old = """        // SAFETY: `Unalign<T>` is a single-field `repr(C, packed)` struct, so
        // its sole field is at offset zero [1]. Thus `self` and its valid `T`
        // field have the same address and provenance. The caller guarantees
        // that this address is aligned for `T`; the returned reference borrows
        // for no longer than `self`, which keeps the storage live and shared.
        //
        // [1] Per https://doc.rust-lang.org/reference/type-layout.html#the-alignment-modifiers:
        //
        //   The alignments of each field, for the purpose of positioning fields,
        //   is the smaller of the specified alignment and the alignment of the
        //   field's type.
"""
        new = """        // SAFETY: `Unalign<T>` is a single-field `repr(C, packed)` struct. The
        // `repr(C)` layout algorithm starts at zero, rounds that offset up for
        // the field's alignment, and places the field there [1]. Zero is already
        // aligned, so the sole field is at offset zero. The caller guarantees
        // the alignment needed to reference that valid `T`; the returned
        // reference borrows the same live storage for no longer than `self`.
        //
        // [1] Per https://doc.rust-lang.org/1.56.0/reference/type-layout.html#reprc-structs:
        //
        //   Start with a current offset of 0 bytes.
        //   ...
        //   The offset of the field is what the current offset is now.
"""
        text = replace_once(text, old, new)
    elif pr == 3676:
        relative = "zerocopy/src/macros.rs"
        path = worktree / relative
        text = path.read_text()
        marker = '#[doc = codegen_section!(\n    header = "h2",\n    bench = "try_transmute",'
        example = """/// A failed transmutation returns ownership of the original source:
///
/// ```
/// use zerocopy::try_transmute;
/// let result: Result<bool, _> = try_transmute!(2u8);
/// assert_eq!(result.unwrap_err().into_src(), 2);
/// ```
///
"""
        text = replace_once(text, marker, example + marker)
    else:
        relative = "zerocopy/src/pointer/inner.rs"
        path = worktree / relative
        text = path.read_text()
        old = """        // SAFETY: As described in the preceding safety comment, `projected_raw`,
        // and thus `projected_non_null`, addresses a subset of `self`'s
        // referent. Thus, `projected_non_null` either:
        // - Addresses zero bytes or,
        // - Addresses a subset of the referent of `self`. In this case, `self`
        //   has provenance for its referent, which lives in an allocation.
        //   Since `projected_non_null` was constructed using a sequence of
        //   provenance-preserving operations, it also has provenance for its
        //   referent and that referent lives in an allocation. By invariant on
        //   `self`, that allocation lives for `'a`.
"""
        new = """        // SAFETY: `C::project` promises that the result addresses a subset of
        // `self`'s referent and preserves its provenance. `NonNull::new_unchecked`
        // preserves that address and provenance. If the projected referent is
        // non-zero-sized, it therefore lies within the same allocation as
        // `self`'s referent, with valid provenance. By invariant on `self`, that
        // allocation lives for `'a`. A zero-sized result needs no allocation.
"""
        text = replace_once(text, old, new)
        start = "        // SAFETY:\n        //\n        // Lemma 0: `raw` either addresses zero bytes, or addresses a subset of\n"
        end = "        unsafe { PtrInner::new(raw) }"
        if text.count(start) != 1 or text.count(end) != 1:
            raise RuntimeError("The with_meta proof boundaries changed")
        first, last = text.index(start), text.index(end)
        if first >= last:
            raise RuntimeError("Invalid with_meta proof range")
        proof = """        // SAFETY: `raw_from_ptr_len` preserves the input address and provenance
        // and uses `meta` for the resulting pointer's metadata. Thus `raw` is
        // the pointer described by this method's precondition. If its referent
        // is non-zero-sized, the caller promises valid provenance for that
        // referent within a Rust allocation which lives for `'a`, satisfying
        // both invariants of `PtrInner::new`. Otherwise, no allocation is needed.
"""
        text = text[:first] + proof + text[last:]
    path.write_text(text)
    git("add", "--", relative, cwd=worktree)
    return relative


def main():
    if os.environ.get("GITHUB_REPOSITORY") != REPO:
        raise RuntimeError("Unexpected repository")
    if os.environ.get("GITHUB_REF") != "refs/heads/joshlf/audit-recovery-runner-20260912":
        raise RuntimeError("Unexpected runner ref")
    pr = int(os.environ["PR_NUMBER"])
    branch, expected, source_branch, parent, title, body = GROUPS[pr]
    metadata = api("pulls/" + str(pr))
    if (metadata["state"] != "open" or metadata["head"]["repo"]["full_name"] != REPO
            or metadata["head"]["ref"] != branch or metadata["head"]["sha"] != expected):
        raise RuntimeError("PR head changed; reconcile before retrying")
    git("fetch", "--no-tags", "origin", "refs/heads/" + source_branch)
    if git("rev-parse", "FETCH_HEAD") != parent:
        raise RuntimeError("Staging parent changed")
    git("merge-base", "--is-ancestor", expected, parent)
    worktree = Path(os.environ["RUNNER_TEMP"]) / ("followup-" + str(pr))
    git("worktree", "add", "--detach", str(worktree), parent)
    relative = edit(pr, worktree)
    paths = git("diff", "--cached", "--name-only", cwd=worktree).splitlines()
    if paths != [relative]:
        raise RuntimeError("Unexpected changed paths")
    git("diff", "--cached", "--check", cwd=worktree)
    print(git("diff", "--cached", cwd=worktree), flush=True)
    identity = dict(os.environ, GIT_AUTHOR_NAME="Josh Liebow-Feeser's Agent",
                    GIT_AUTHOR_EMAIL="agent@joshlf.invalid",
                    GIT_COMMITTER_NAME="Josh Liebow-Feeser's Agent",
                    GIT_COMMITTER_EMAIL="agent@joshlf.invalid")
    message = title + "\n\n" + body + "\n\nAgent-Authored-By: AI agent acting on Josh Liebow-Feeser's behalf"
    git("commit", "-m", message, cwd=worktree, env=identity)
    head = git("rev-parse", "HEAD", cwd=worktree)
    run = os.environ["GITHUB_RUN_ID"]
    if not run.isdecimal():
        raise RuntimeError("Unexpected run ID")
    staging = "refs/heads/joshlf/audit-followup-" + str(pr) + "-" + run
    basic = base64.b64encode(("x-access-token:" + os.environ["GH_TOKEN"]).encode()).decode()
    push_env = dict(os.environ, GIT_CONFIG_COUNT="1",
                    GIT_CONFIG_KEY_0="http.https://github.com/.extraheader",
                    GIT_CONFIG_VALUE_0="AUTHORIZATION: basic " + basic)
    if git("ls-remote", "--heads", "origin", staging, cwd=worktree, env=push_env):
        raise RuntimeError("Refusing to overwrite a staging ref")
    git("push", "origin", "HEAD:" + staging, cwd=worktree, env=push_env)
    if git("ls-remote", "--heads", "origin", staging, cwd=worktree, env=push_env).split()[0] != head:
        raise RuntimeError("Staging readback failed")
    with open(os.environ["GITHUB_OUTPUT"], "a") as output:
        output.write("worktree=" + str(worktree) + "\nhead=" + head + "\n")
    result = {"pr": pr, "parent": parent, "head": head, "staging_ref": staging,
              "pr_head_unchanged": expected, "changed_files": paths,
              "file_sha256": hashlib.sha256((worktree / relative).read_bytes()).hexdigest()}
    print(json.dumps(result, indent=2), flush=True)
    with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as summary:
        summary.write("```json\n" + json.dumps(result, indent=2) + "\n```\n")


if __name__ == "__main__":
    main()
