#!/usr/bin/env python3
"""Count and classify `#adaptation_note` uses in an extracted Mathlib source tree.

Usage: python3 adaptation_notes.py <mathlib-root>
Excludes Mathlib/Tactic/AdaptationNote.lean (the command's own definition and self-tests).
"""
import collections, pathlib, re, sys

root = pathlib.Path(sys.argv[1])
note_re = re.compile(r"#adaptation_note\b(?:\s*/--(.*?)-/)?", re.S)
nightly_re = re.compile(r"nightly-(\d{4})-(\d{2})-(\d{2})")
ver_re = re.compile(r"\bv?4\.(\d+)\.\d+(?:-rc\d+)?")
pr_re = re.compile(r"lean4#(\d+)|leanprover/lean4/pull/(\d+)")
tot = 0; files = set(); by_dir = collections.Counter(); years = collections.Counter()
odd = []; backcompat = collections.Counter(); kinds = collections.Counter(); no_doc = 0; minor = collections.Counter()
for p in sorted(root.rglob("*.lean")):
    rel = p.relative_to(root).as_posix()
    if rel == "Mathlib/Tactic/AdaptationNote.lean" or rel.startswith(".lake/"):
        continue
    txt = p.read_text(encoding="utf-8", errors="replace")
    for m in note_re.finditer(txt):
        line_start = txt.rfind("\n", 0, m.start()) + 1
        prefix = txt[line_start:m.start()]
        # Skip textual mentions: inside backticks/strings, after a line comment, or in prose.
        if prefix.endswith(("`", '"')) or "--" in prefix or "!" in prefix or "/-" in prefix or '"' in prefix:
            continue
        if prefix.strip() not in ("", "·", "<;>", "(", "by", ":=", "· (", "|"):
            odd.append(f"{rel}:{txt.count(chr(10), 0, m.start())+1}: {prefix.strip()!r}")
        tot += 1; files.add(rel); by_dir[rel.split("/")[0]] += 1
        doc = m.group(1) or ""
        if not doc: no_doc += 1
        k = []
        n = nightly_re.findall(doc)
        if n:
            k.append("nightly-date"); years[n[0][0]] += 1
        v = ver_re.findall(doc)
        if v:
            k.append("release-version"); minor[int(v[0])] += 1
        if pr_re.search(doc): k.append("lean4-PR-ref")
        if not n and re.search(r"\b20\d\d-\d\d-\d\d\b", doc): k.append("bare-date")
        after = txt[m.end():m.end()+200]
        if re.match(r"\s*set_option\s+backward\.", after): backcompat[re.match(r"\s*set_option\s+(backward\.[\w.]+)", after).group(1)] += 1
        kinds[tuple(k) if k else ("no-version-ref",)] += 1
print("total_notes", tot)
print("notes_with_unusual_prefix (kept, listed for audit)", len(odd)); [print("  ", o) for o in odd[:20]]
print("files_with_notes", len(files))
print("by_top_dir", dict(by_dir))
print("notes_without_doc_comment", no_doc)
print("reference_kinds", {"+".join(k): c for k, c in kinds.most_common()})
print("notes_directly_followed_by_set_option_backward", sum(backcompat.values()), dict(backcompat.most_common()))
print("first_nightly_year_cited", dict(sorted(years.items())))
print("first_release_minor_cited(4.x)", dict(sorted(minor.items())))
