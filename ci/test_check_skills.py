# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for ci/check_skills.py."""

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

CI_DIR = Path(__file__).resolve().parent
REPO_ROOT = CI_DIR.parent
if str(CI_DIR) not in sys.path:
    sys.path.insert(0, str(CI_DIR))

import check_skills  # noqa: E402


COMMIT_SHA = "b563468a8148df117283494915cee5b6561cc47f"
CRR_BLOCK = (
    "<!-- code-review-rules:begin -->\n"
    "## Code Review Rules\n\n"
    "Rule one.\n"
    "<!-- code-review-rules:end -->\n"
)


def write_skill_md(
    skill_dir: Path,
    name: str,
    description: str = "Exercise skill validation.",
    body: str = "# Heading\n\nPlain body.\n",
) -> Path:
    skill_dir.mkdir(parents=True, exist_ok=True)
    path = skill_dir / "SKILL.md"
    content = (
        f"---\nname: {name}\ndescription: >-\n  {description}\n---\n\n{body}"
    )
    path.write_text(content, encoding="utf-8")
    os.chmod(path, 0o644)
    return path


def lock_entry(file_path: Path, rel_posix: str, mode: str = "100644") -> dict:
    raw = file_path.read_bytes()
    return {
        "path": rel_posix,
        "mode": mode,
        "bytes": len(raw),
        "sha256": hashlib.sha256(raw).hexdigest(),
    }


class CheckSkillsTests(unittest.TestCase):
    def build_fixture(self, root: Path, *, init_git: bool = False) -> Path:
        skills_dir = root / "skills"
        anneal_skills = root / "anneal" / "skills"
        cargo_anneal_skills = (
            root / "anneal" / "trusted" / "cargo-anneal" / "skills"
        )
        agents_dir = root / "anneal" / ".agents"
        skills_dir.mkdir(parents=True)
        anneal_skills.mkdir(parents=True)
        cargo_anneal_skills.mkdir(parents=True)
        agents_dir.mkdir(parents=True)

        (skills_dir / "README.md").write_text(
            "# Skills\n\nSee [`vendored-pkg`](vendored-pkg/SKILL.md#heading) "
            "and [`unsafe-rust`](unsafe-rust/SKILL.md).\n",
            encoding="utf-8",
        )
        (anneal_skills / "README.md").write_text(
            "# Anneal skills\n\nSee "
            "[`policy-review`](policy-review/SKILL.md#heading) and "
            "[shared skills](../../skills/README.md#skills).\n",
            encoding="utf-8",
        )

        # Vendored package with a Markdown reference.
        vendored_dir = skills_dir / "vendored-pkg"
        vendored_md = write_skill_md(
            vendored_dir,
            "vendored-pkg",
            body=(
                "# Heading\n\nRun [helper](references/helper.md). "
                "Ignore `[code](missing.md)` and:\n\n"
                "```markdown\n[ignored](also-missing.md)\n```\n"
                "<!-- [commented](still-missing.md) -->\n"
            ),
        )
        references = vendored_dir / "references"
        references.mkdir()
        helper = references / "helper.md"
        helper.write_text("# Reference\n", encoding="utf-8")

        # Repo-owned root skill using double-quoted description + ref link.
        local_dir = skills_dir / "unsafe-rust"
        local_dir.mkdir()
        (local_dir / "SKILL.md").write_text(
            '---\nname: unsafe-rust\ndescription: "Local repo skill."\n---\n\n'
            "# Local Heading\n\nSee [guide][guide-ref].\n\n"
            "[guide-ref]: ../README.md#skills\n",
            encoding="utf-8",
        )

        # Anneal pure-Markdown policy skill.
        write_skill_md(
            anneal_skills / "policy-review",
            "policy-review",
            body=(
                "# Heading\n\nCompose with "
                "[`vendored-pkg`]("
                "../../../skills/vendored-pkg/SKILL.md#heading).\n"
            ),
        )

        # CLI-bundled cargo-anneal skill.
        write_skill_md(
            cargo_anneal_skills / "cargo-anneal",
            "cargo-anneal",
            description="Verify Rust code with cargo-anneal.",
        )

        lock_data = {
            "schema": 1,
            "packages": {
                "vendored-pkg": {
                    "upstream_repo": "https://github.com/joshlf/skills",
                    "upstream_path": "vendored_pkg",
                    "upstream_commit": COMMIT_SHA,
                    "omitted_upstream_paths": ["references/NOTES.md"],
                    "local_modifications": [
                        "SKILL.md: removed link to omitted references/NOTES.md."
                    ],
                    "files": [
                        lock_entry(vendored_md, "SKILL.md", "100644"),
                        lock_entry(helper, "references/helper.md"),
                    ],
                }
            },
        }
        lock_path = skills_dir / "vendor-lock.json"
        lock_path.write_text(
            json.dumps(lock_data, indent=2) + "\n", encoding="utf-8"
        )

        (root / "anneal" / "AGENTS.md").write_text(
            "# Anneal\n\n" + CRR_BLOCK, encoding="utf-8"
        )
        (root / "anneal" / ".gemini").mkdir()
        (root / "anneal" / ".gemini" / "styleguide.md").write_text(
            "# Styleguide\n\n" + CRR_BLOCK, encoding="utf-8"
        )

        (agents_dir / "skills.json").write_text(
            json.dumps(
                {
                    "entries": [
                        {"path": "../skills"},
                        {"path": "../trusted/cargo-anneal/skills"},
                        {"path": "../../skills"},
                    ]
                },
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )

        if init_git:
            self.git(root, "init", "-q", "--template=")
            self.git(root, "add", ".")

        return root

    def git(self, cwd: Path, *args: str) -> None:
        subprocess.run(
            [
                "git",
                "-c",
                "core.hooksPath=/dev/null",
                "-c",
                "core.fsmonitor=false",
                *args,
            ],
            cwd=cwd,
            env=check_skills.git_environment(),
            check=True,
            capture_output=True,
            text=True,
        )

    def assert_fails_with(self, repo: Path, expected_substring: str) -> None:
        with self.assertRaises(check_skills.SkillCheckError) as ctx:
            check_skills.check_repository(repo)
        self.assertIn(expected_substring, str(ctx.exception))

    def test_live_repository_passes(self) -> None:
        self.assertEqual(
            check_skills.main(["--repo-root", str(REPO_ROOT)]), 0
        )

    def test_clean_fixture_passes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self.build_fixture(Path(tmp), init_git=True)
            check_skills.check_repository(repo)

    def test_fixture_git_ignores_repository_local_hook_environment(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            with patch.dict(os.environ, {
                "GIT_DIR": str(root / "outside.git"),
                "GIT_INDEX_FILE": str(root / "outside-index"),
            }):
                repo = self.build_fixture(root / "fixture", init_git=True)
                check_skills.check_repository(repo)
                helper = "skills/vendored-pkg/references/helper.md"
                self.git(repo, "update-index", "--chmod=+x", helper)
                os.chmod(repo / helper, 0o644)
                self.assert_fails_with(repo, "Git index mode 100755")
            self.assertTrue((repo / ".git/index").is_file())
            self.assertFalse((root / "outside.git").exists())
            self.assertFalse((root / "outside-index").exists())

    def test_vendored_hash_and_size_mismatch_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self.build_fixture(Path(tmp))
            skill_md = repo / "skills" / "vendored-pkg" / "SKILL.md"
            text = skill_md.read_text(encoding="utf-8")
            # Same byte length, different SHA-256.
            mutated = text.replace("Run [helper]", "run [helper]")
            self.assertNotEqual(mutated, text)
            skill_md.write_text(mutated, encoding="utf-8")
            self.assert_fails_with(repo, "sha256")

            # Different byte length.
            skill_md.write_text(text + "\nextra\n", encoding="utf-8")
            self.assert_fails_with(repo, "byte count")

    def test_unexpected_or_missing_files_in_locked_package_fail(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self.build_fixture(Path(tmp))
            extra = repo / "skills" / "vendored-pkg" / "UNTRACKED.md"
            extra.write_text("# Stray\n", encoding="utf-8")
            self.assert_fails_with(repo, "unexpected/untracked file(s)")
            extra.unlink()

            helper = (
                repo / "skills" / "vendored-pkg" / "references" / "helper.md"
            )
            helper.unlink()
            self.assert_fails_with(repo, "missing locked file(s)")

    def test_disk_and_git_mode_mismatches_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self.build_fixture(Path(tmp), init_git=True)
            helper = repo / "skills" / "vendored-pkg" / "references" / "helper.md"
            os.chmod(helper, 0o755)
            self.assert_fails_with(repo, "on-disk mode 100755")
            os.chmod(helper, 0o644)

            # Mutate the Git index mode without changing the lockfile; restore
            # the working-tree chmod so we specifically exercise the Git guard.
            self.git(
                repo,
                "update-index",
                "--chmod=+x",
                "skills/vendored-pkg/references/helper.md",
            )
            os.chmod(helper, 0o644)
            self.assert_fails_with(repo, "Git index mode 100755")

    def test_untracked_locked_file_in_tracked_repo_fails(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self.build_fixture(Path(tmp), init_git=True)
            self.git(
                repo,
                "rm",
                "--cached",
                "-q",
                "skills/vendored-pkg/references/helper.md",
            )
            self.assert_fails_with(repo, "locked file(s) not tracked in Git")

    def test_symlinks_rejected_everywhere(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self.build_fixture(Path(tmp))
            link = repo / "skills" / "unsafe-rust" / "link.md"
            link.symlink_to("../README.md")
            self.assert_fails_with(repo, "symlink is forbidden")
            link.unlink()

            outside = repo / "outside.md"
            outside.write_text("# Outside\n", encoding="utf-8")
            bridge = repo / "bridge"
            bridge.symlink_to(".")
            md = repo / "skills" / "unsafe-rust" / "SKILL.md"
            md.write_text(
                md.read_text(encoding="utf-8")
                + "\n[via-symlink](../../bridge/outside.md#outside)\n",
                encoding="utf-8",
            )
            self.assert_fails_with(repo, "symlink forbidden: bridge")

    def test_case_collision_and_unicode_control_chars_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self.build_fixture(Path(tmp))
            d1 = repo / "skills" / "unsafe-rust" / "references"
            d2 = repo / "skills" / "unsafe-rust" / "References"
            d1.mkdir()
            (d1 / "a.md").write_text("# A\n", encoding="utf-8")
            try:
                d2.mkdir()
            except FileExistsError:
                # Case-insensitive host filesystem; test file-level NFC/case
                # check directly via check_skills.scan_tree not needed.
                pass
            else:
                (d2 / "b.md").write_text("# B\n", encoding="utf-8")
                self.assert_fails_with(repo, "case/NFC path collision")
                (d2 / "b.md").unlink()
                d2.rmdir()

            # Bidi RLO character U+202E in Markdown content fails closed.
            (d1 / "a.md").write_text("# A \u202ehidden\n", encoding="utf-8")
            self.assert_fails_with(
                repo, "forbidden Unicode control/bidi character U+202E"
            )

    def test_frontmatter_and_duplicate_skill_names_validated(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self.build_fixture(Path(tmp))
            bad_md = repo / "skills" / "unsafe-rust" / "SKILL.md"

            bad_md.write_text("# No frontmatter\n", encoding="utf-8")
            self.assert_fails_with(repo, "missing opening '---'")

            bad_md.write_text(
                "---\nname: wrong-name\ndescription: ok\n---\n# H\n",
                encoding="utf-8",
            )
            self.assert_fails_with(repo, "does not match directory")

            bad_md.write_text(
                "---\nname: unsafe-rust\ndescription: >-\n  \n---\n# H\n",
                encoding="utf-8",
            )
            self.assert_fails_with(repo, "empty block scalar")

            bad_md.write_text(
                "---\nname: unsafe-rust\ndescription: a\ndescription: b\n---\n",
                encoding="utf-8",
            )
            self.assert_fails_with(repo, "duplicate frontmatter key")

            # Restore unsafe-rust, then add a colliding skill in anneal/skills.
            bad_md.write_text(
                "---\nname: unsafe-rust\ndescription: ok\n---\n# H\n",
                encoding="utf-8",
            )
            write_skill_md(
                repo / "anneal" / "skills" / "unsafe-rust", "unsafe-rust"
            )
            self.assert_fails_with(repo, "duplicate skill name(s)")

    def test_broken_links_and_anchors_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self.build_fixture(Path(tmp))
            md = repo / "skills" / "unsafe-rust" / "SKILL.md"
            base = "---\nname: unsafe-rust\ndescription: ok\n---\n\n# H\n\n"

            md.write_text(base + "[missing](nope.md)\n", encoding="utf-8")
            self.assert_fails_with(repo, "target does not exist")

            md.write_text(
                base + "[bad-anchor](../README.md#nonexistent)\n",
                encoding="utf-8",
            )
            self.assert_fails_with(repo, "broken heading anchor #nonexistent")

            md.write_text(base + "[empty]()\n", encoding="utf-8")
            self.assert_fails_with(repo, "empty Markdown link destination")

            md.write_text(
                base + "[escape](../../../outside.md)\n", encoding="utf-8"
            )
            self.assert_fails_with(repo, "path escapes repository root")

            md.write_text(base + "[undef][missing-ref]\n", encoding="utf-8")
            self.assert_fails_with(
                repo, "undefined Markdown link reference 'missing-ref'"
            )

    def test_both_skill_roots_reject_scripts_and_executables(self) -> None:
        for skill in (
            "skills/unsafe-rust",
            "anneal/skills/policy-review",
            "anneal/trusted/cargo-anneal/skills/cargo-anneal",
        ):
            for filename, content, make_exec in (
                ("helper.py", "print(1)\n", False),
                ("run.sh", "echo hi\n", False),
                ("notes.txt", "#!/bin/sh\necho hi\n", False),
                ("guide.md", "# Guide\n", True),
            ):
                with self.subTest(skill=skill, filename=filename), tempfile.TemporaryDirectory() as tmp:
                    repo = self.build_fixture(Path(tmp))
                    p = repo / skill / filename
                    p.write_text(content, encoding="utf-8")
                    if make_exec:
                        os.chmod(p, 0o755)
                    self.assert_fails_with(
                        repo, "only non-executable documentation and data"
                    )

    def test_both_skill_roots_reject_forbidden_config_paths(self) -> None:
        for skill in (
            "skills/unsafe-rust",
            "anneal/skills/policy-review",
            "anneal/trusted/cargo-anneal/skills/cargo-anneal",
        ):
            for name in (
                "AGENTS.override.md", "nested/.cargo/config.toml",
                "nested/.agents/skills.json", "nested/rust-toolchain.toml",
            ):
                with self.subTest(skill=skill, name=name), tempfile.TemporaryDirectory() as tmp:
                    repo = self.build_fixture(Path(tmp))
                    path = repo / skill / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text("test config\n", encoding="utf-8")
                    self.assert_fails_with(repo, "forbidden skill path")

    def test_remaining_vendored_directory_cannot_lose_its_lock(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self.build_fixture(Path(tmp))
            other = write_skill_md(repo / "skills/other-vendored", "other-vendored")
            lock = repo / "skills/vendor-lock.json"
            data = json.loads(lock.read_text(encoding="utf-8"))
            vendored = data["packages"]["vendored-pkg"]
            data["packages"] = {
                "other-vendored": {**vendored, "files": [lock_entry(other, "SKILL.md")]},
                "vendored-pkg": vendored,
            }
            lock.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
            check_skills.check_repository(repo)
            del data["packages"]["vendored-pkg"]
            lock.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
            self.assert_fails_with(repo, "unlocked skill directories: ['vendored-pkg']")

    def test_balanced_and_escaped_inline_link_destinations(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self.build_fixture(Path(tmp))
            md = repo / "skills/unsafe-rust/SKILL.md"
            header = md.read_text(encoding="utf-8")
            (repo / "guide(foo").write_text("Wrong path\n", encoding="utf-8")
            md.write_text(
                header + "[Guide [draft]](../../guide(foo).md)\n", encoding="utf-8",
            )
            self.assert_fails_with(repo, "target does not exist")

            (repo / "guide(foo).md").write_text("# Guide\n", encoding="utf-8")
            (repo / "logo.png").write_bytes(b"test image target")
            (repo / "guide space.md").write_text(
                "[ref]: README.md\n---\n\n#tag\n====\n\nParagraph\n***\n---\n",
                encoding="utf-8",
            )
            md.write_text(
                header + '# See [Guide [draft]](../../guide(foo).md "title ) here")\n'
                + "[heading](#see-guide-draft)\n"
                + "# [a![](../../logo.png)b](../../guide(foo).md)\n"
                + "[nested image heading](#ab)\n"
                + r"[escaped](../../guide\(foo\).md#guide)" + "\n\n"
                + "[encoded](../../guide%20space.md#tag)\n\n"
                + "[guide space][space]\n\n"
                + "[space]: <../../guide space.md#tag>\n",
                encoding="utf-8",
            )
            check_skills.check_repository(repo)
            valid = md.read_text(encoding="utf-8")
            for missing in ("ref-readmemd", "paragraph-"):
                with self.subTest(missing=missing):
                    md.write_text(
                        valid + f"\n[not a heading](../../guide%20space.md#{missing})\n",
                        encoding="utf-8",
                    )
                    self.assert_fails_with(repo, f"broken heading anchor #{missing}")

    def test_strict_json_and_skills_json_discovery_checks(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self.build_fixture(Path(tmp))
            cfg = repo / "anneal" / ".agents" / "skills.json"

            cfg.write_text(
                '{"entries": [{"path": "../skills"}], "entries": []}\n',
                encoding="utf-8",
            )
            self.assert_fails_with(repo, "duplicate JSON key 'entries'")

            cfg.write_text(
                '{"entries": [{"path": "../skills"}]}\n', encoding="utf-8"
            )
            self.assert_fails_with(
                repo, "expected resolved skill directories"
            )

            # Restore skills.json and test non-canonical vendor-lock.json.
            cfg.write_text(
                json.dumps(
                    {
                        "entries": [
                            {"path": "../skills"},
                            {"path": "../trusted/cargo-anneal/skills"},
                            {"path": "../../skills"},
                        ]
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            lock = repo / "skills" / "vendor-lock.json"
            lock.write_text(
                lock.read_text(encoding="utf-8").rstrip("\n"),
                encoding="utf-8",
            )
            self.assert_fails_with(repo, "non-canonical JSON formatting")

    def test_symlink_dotdot_and_parent_bounce_escapes_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            outside = Path(tmp) / "outside_evil" / "sub1" / "sub2"
            outside.mkdir(parents=True)
            (Path(tmp) / "outside_evil" / "anneal" / "skills").mkdir(
                parents=True
            )

            repo = self.build_fixture(Path(tmp) / "zerocopy")
            cfg = repo / "anneal" / ".agents" / "skills.json"

            # Probe A: `<symlink>/..` in anneal/.agents/skills.json.
            escape_link = repo / "anneal" / "escape"
            escape_link.symlink_to(outside)
            cfg.write_text(
                json.dumps(
                    {
                        "entries": [
                            {"path": "../escape/../../anneal/skills"},
                            {"path": "../trusted/cargo-anneal/skills"},
                            {"path": "../../skills"},
                        ]
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            self.assert_fails_with(repo, "symlink forbidden: anneal/escape")
            escape_link.unlink()
            cfg.write_text(
                json.dumps(
                    {
                        "entries": [
                            {"path": "../skills"},
                            {"path": "../trusted/cargo-anneal/skills"},
                            {"path": "../../skills"},
                        ]
                    }
                )
                + "\n",
                encoding="utf-8",
            )

            # Probe B: `../../../<repo_name>/...` parent-directory bounce.
            md = repo / "skills" / "unsafe-rust" / "SKILL.md"
            base = "---\nname: unsafe-rust\ndescription: ok\n---\n\n# H\n\n"
            md.write_text(
                base + "[bounce](../../../zerocopy/skills/README.md#skills)\n",
                encoding="utf-8",
            )
            self.assert_fails_with(repo, "path escapes repository root")

            # Probe C: `<symlink>/..` inside a Markdown relative link.
            bridge = repo / "bridge"
            bridge.symlink_to(outside)
            md.write_text(
                base + "[via-bridge](../../bridge/../skills/README.md)\n",
                encoding="utf-8",
            )
            self.assert_fails_with(repo, "symlink forbidden: bridge")

    def test_multiline_links_and_html_comment_code_interactions(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self.build_fixture(Path(tmp))
            md = repo / "skills" / "unsafe-rust" / "SKILL.md"
            base = "---\nname: unsafe-rust\ndescription: ok\n---\n\n# H\n\n"

            # Valid wrapped multiline link + `"<!--"` inside fenced code +
            # `` `<!--` `` inside inline code must pass cleanly.
            md.write_text(
                base
                + "See [shared\nskills](../README.md#skills) and `<!--`.\n\n"
                + "```python\nif text.startswith('<!--'):\n    pass\n```\n\n"
                + "<!-- valid trailing comment -->\n",
                encoding="utf-8",
            )
            check_skills.check_repository(repo)

            # Probe D1: wrapped multiline broken inline link must fail closed.
            md.write_text(
                base + "See [wrapped\nbroken](missing.md#bad).\n",
                encoding="utf-8",
            )
            self.assert_fails_with(repo, "target does not exist")

            # Probe D2: wrapped multiline undefined reference link must fail.
            md.write_text(
                base + "See [wrapped\nref][undefined-label].\n",
                encoding="utf-8",
            )
            self.assert_fails_with(
                repo, "undefined Markdown link reference 'undefined-label'"
            )

            # Probe E1: inline `` `<!--` `` before a real comment must NOT
            # mask a broken link in between.
            md.write_text(
                base
                + "Reject unclosed `<!--` markers.\n\n"
                + "[broken](totally-missing.md#bad)\n\n"
                + "<!-- legitimate comment -->\n",
                encoding="utf-8",
            )
            self.assert_fails_with(repo, "target does not exist")

    def test_cargo_anneal_skill_root_and_cross_root_collisions(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self.build_fixture(Path(tmp))
            cargo_skills = (
                repo / "anneal" / "trusted" / "cargo-anneal" / "skills"
            )
            extra_top = cargo_skills / "NOTES.md"
            extra_top.write_text("# Stray\n", encoding="utf-8")
            self.assert_fails_with(repo, "unexpected top-level file")
            extra_top.unlink()

            write_skill_md(
                repo / "anneal" / "skills" / "cargo-anneal", "cargo-anneal"
            )
            self.assert_fails_with(repo, "duplicate skill name(s)")

    def test_skill_line_limit_and_grandfathered_caps(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self.build_fixture(Path(tmp))
            # Non-grandfathered skill at 300 lines passes; at 301 fails.
            md = repo / "anneal" / "skills" / "policy-review" / "SKILL.md"
            header = (
                "---\nname: policy-review\ndescription: ok\n---\n\n# Heading\n"
            )
            pad_300 = header + ("line\n" * (300 - len(header.splitlines())))
            self.assertEqual(len(pad_300.splitlines()), 300)
            md.write_text(pad_300, encoding="utf-8")
            check_skills.check_repository(repo)

            md.write_text(pad_300 + "overflow\n", encoding="utf-8")
            self.assert_fails_with(repo, "exceeding limit of 300")
            md.write_text(pad_300, encoding="utf-8")

            # Grandfathered `skills/unsafe-rust/SKILL.md` capped at 364 lines.
            unsafe_md = repo / "skills" / "unsafe-rust" / "SKILL.md"
            u_hdr = "---\nname: unsafe-rust\ndescription: ok\n---\n\n# H\n"
            cap = check_skills.GRANDFATHERED_SKILL_LINE_CAPS[
                "skills/unsafe-rust/SKILL.md"
            ]
            u_at_cap = u_hdr + ("line\n" * (cap - len(u_hdr.splitlines())))
            unsafe_md.write_text(u_at_cap, encoding="utf-8")
            check_skills.check_repository(repo)

            unsafe_md.write_text(u_at_cap + "bloat\n", encoding="utf-8")
            self.assert_fails_with(repo, f"exceeding limit of {cap}")

    def test_agents_md_budget_links_and_override_ban(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self.build_fixture(Path(tmp))
            root_agents = repo / "AGENTS.md"
            anneal_agents = repo / "anneal" / "AGENTS.md"

            # Broken link in root `AGENTS.md` fails closed.
            root_agents.write_text(
                "# Root\n\nSee [broken](does-not-exist.md).\n",
                encoding="utf-8",
            )
            self.assert_fails_with(repo, "target does not exist")

            root_agents.write_text("# Root\n", encoding="utf-8")
            check_skills.check_repository(repo)

            # `AGENTS.override.md` rejected at root and under `anneal/`.
            root_override = repo / "AGENTS.override.md"
            root_override.write_text("# Override\n", encoding="utf-8")
            self.assert_fails_with(repo, "repository-root override is forbidden")
            root_override.unlink()

            sub_dir = repo / "anneal" / "sub"
            sub_dir.mkdir(parents=True)
            sub_override = sub_dir / "AGENTS.override.md"
            sub_override.write_text("# Override\n", encoding="utf-8")
            self.assert_fails_with(repo, "AGENTS.override.md is forbidden")
            sub_override.unlink()

            # Symlinked pruned directory under `anneal/` fails closed.
            outside_target = Path(tmp) / "outside_target"
            outside_target.mkdir()
            symlink_target = repo / "anneal" / "target"
            symlink_target.symlink_to(outside_target)
            self.assert_fails_with(repo, "symlink forbidden: anneal/target")
            symlink_target.unlink()

            # Budget `< 31744`: exact `31743` passes, `31744` fails.
            root_len = root_agents.lstat().st_size
            budget = check_skills.CODEX_AGENTS_MD_BUDGET_BYTES
            block = CRR_BLOCK.encode("utf-8")
            pad = budget - 1 - root_len - len(block)
            anneal_agents.write_bytes(block + b"a" * pad)
            check_skills.check_repository(repo)

            anneal_agents.write_bytes(block + b"a" * (pad + 1))
            self.assert_fails_with(repo, f"Codex budget of {budget} B")

    def test_code_review_rules_parity(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self.build_fixture(Path(tmp))
            agents = repo / "anneal" / "AGENTS.md"
            style = repo / "anneal" / ".gemini" / "styleguide.md"

            # Matching blocks pass even when surrounding text differs.
            style.write_text(
                "# Other preamble\n\n" + CRR_BLOCK + "\nTrailer.\n",
                encoding="utf-8",
            )
            check_skills.check_repository(repo)

            # Drift inside the block fails and names the first bad line.
            style.write_text(
                CRR_BLOCK.replace("Rule one.", "Rule one!"), encoding="utf-8"
            )
            self.assert_fails_with(repo, "differs from `anneal/AGENTS.md`")
            self.assert_fails_with(repo, "at block line 4")

            # Missing, duplicated, or reordered markers fail closed.
            style.write_text("# Styleguide\n", encoding="utf-8")
            self.assert_fails_with(repo, "code-review-rules-parity: expected one")
            style.write_text(CRR_BLOCK + CRR_BLOCK, encoding="utf-8")
            self.assert_fails_with(repo, "code-review-rules-parity: expected one")
            style.write_text(
                "<!-- code-review-rules:end -->\n"
                "<!-- code-review-rules:begin -->\n",
                encoding="utf-8",
            )
            self.assert_fails_with(repo, "code-review-rules-parity: expected one")

            # Deleting either mirror, or replacing it with a symlink, fails.
            style.unlink()
            self.assert_fails_with(
                repo, "target does not exist: anneal/.gemini/styleguide.md"
            )
            style.symlink_to("../AGENTS.md")
            self.assert_fails_with(
                repo, "symlink forbidden: anneal/.gemini/styleguide.md"
            )
            style.unlink()
            style.write_text(CRR_BLOCK, encoding="utf-8")
            agents.unlink()
            self.assert_fails_with(
                repo, "target does not exist: anneal/AGENTS.md"
            )

    def test_proof_scaling_and_cargo_anneal_boundary_sync(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = self.build_fixture(Path(tmp))
            tb_path = repo / "anneal" / "trusted" / "audit" / "TrustedBoundary.lean"
            tb_path.parent.mkdir(parents=True)
            tb_base = (
                "def allowedTheoryTacticKinds : List Name := [\n"
                "  ``Parser.Term.byTactic,\n"
                "  `Lean.Parser.Tactic.apply,\n"
                "  `Lean.Parser.Tactic.exact,\n"
                "  `Lean.Parser.Tactic.«tactic_<;>_»,\n"
                "  `Lean.Parser.Tactic.«tacticNomatch_,,»,\n"
                "  `tacticFunext___\n"
                "]\n"
            )
            tb_path.write_text(tb_base, encoding="utf-8")

            theory_dir = repo / "anneal" / "theory" / "Anneal"
            theory_dir.mkdir(parents=True)
            (theory_dir / "LinearArith.lean").write_text("-- ok\n", encoding="utf-8")
            (theory_dir / "PureLift.lean").write_text("-- ok\n", encoding="utf-8")
            manifest = repo / "anneal" / "theory" / "bundle-manifest.json"
            manifest.write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "modules": [
                            {"path": "theory/Anneal/LinearArith.lean", "sha256": "0" * 64}
                        ],
                    }
                )
                + "\n",
                encoding="utf-8",
            )

            ps_body = (
                "# Proof Scaling\n\n"
                "<!-- pass1-bundled-modules:begin -->\n"
                "`Anneal.LinearArith`\n"
                "<!-- pass1-bundled-modules:end -->\n\n"
                "Also `Anneal.PureLift` in-tree.\n\n"
                "<!-- pass1-tactic-allowlist:begin -->\n"
                "`apply`, `exact`, `<;>`, `nomatch`, `funext`\n"
                "<!-- pass1-tactic-allowlist:end -->\n"
            )
            ps_md = write_skill_md(
                repo / "anneal" / "skills" / "proof-scaling",
                "proof-scaling",
                body=ps_body,
            )
            full_ps = ps_md.read_text(encoding="utf-8")
            (repo / "anneal" / "skills" / "README.md").write_text(
                "# Anneal skills\n\nSee "
                "[`policy-review`](policy-review/SKILL.md#heading), "
                "[`proof-scaling`](proof-scaling/SKILL.md#proof-scaling), and "
                "[shared skills](../../skills/README.md#skills).\n",
                encoding="utf-8",
            )
            ca_md = (
                repo
                / "anneal"
                / "trusted"
                / "cargo-anneal"
                / "skills"
                / "cargo-anneal"
                / "SKILL.md"
            )
            ca_base = (
                "---\nname: cargo-anneal\ndescription: ok\n---\n\n"
                "# CA\n\nUse `Anneal.LinearArith`.\n"
            )
            ca_md.write_text(ca_base, encoding="utf-8")
            check_skills.check_repository(repo)

            # Missing tactic in `proof-scaling` fails closed.
            ps_md.write_text(
                full_ps.replace(", `funext`", ""), encoding="utf-8"
            )
            self.assert_fails_with(repo, "Pass-1 tactic allowlist out of sync")
            ps_md.write_text(full_ps, encoding="utf-8")

            # Unmapped parser kind in `TrustedBoundary.lean` fails closed.
            tb_path.write_text(
                tb_base.replace("`tacticFunext___", "`tacticFunext___, `Lean.Parser.Tactic.omega"),
                encoding="utf-8",
            )
            self.assert_fails_with(repo, "unmapped allowedTheoryTacticKinds entry")

            # Comment containing `def allowedTheoryTacticKinds` or `]` must not
            # mis-anchor or prematurely terminate parsing.
            tb_with_comments = (
                "/-- Docstring mentioning def allowedTheoryTacticKinds : List Name := [ -/\n"
                + tb_base.replace(
                    "`Lean.Parser.Tactic.exact,",
                    "-- comment with closing ]\n  `Lean.Parser.Tactic.exact,",
                )
            )
            tb_path.write_text(tb_with_comments, encoding="utf-8")
            check_skills.check_repository(repo)
            tb_path.write_text(tb_base, encoding="utf-8")

            # Missing or symlinked bundled module file in `bundle-manifest.json`
            # fails closed even before checking non-bundled modules.
            (theory_dir / "LinearArith.lean").unlink()
            self.assert_fails_with(repo, "bundled module file missing")
            outside_b = Path(tmp) / "outside_bundled.lean"
            outside_b.write_text("-- bad\n", encoding="utf-8")
            (theory_dir / "LinearArith.lean").symlink_to(outside_b)
            self.assert_fails_with(repo, "symlink forbidden")
            (theory_dir / "LinearArith.lean").unlink()
            (theory_dir / "LinearArith.lean").write_text("-- ok\n", encoding="utf-8")
            check_skills.check_repository(repo)

            # Unbundled module listed in `pass1-bundled-modules` fails closed.
            ps_md.write_text(
                full_ps.replace(
                    "`Anneal.LinearArith`", "`Anneal.LinearArith`, `Anneal.PureLift`"
                ),
                encoding="utf-8",
            )
            self.assert_fails_with(repo, "bundled modules missing")
            ps_md.write_text(full_ps, encoding="utf-8")

            # Nonexistent `Anneal.Phantom` cited in `proof-scaling` or `cargo-anneal` fails.
            ps_md.write_text(full_ps + "Use `Anneal.Phantom`.\n", encoding="utf-8")
            self.assert_fails_with(repo, "missing at anneal/theory/Anneal/Phantom.lean")
            ps_md.write_text(full_ps, encoding="utf-8")

            ca_md.write_text(ca_base + "Use `Anneal.Phantom`.\n", encoding="utf-8")
            self.assert_fails_with(repo, "missing from anneal/theory/bundle-manifest.json")
            ca_md.write_text(ca_base, encoding="utf-8")

            # Ancestor directory symlink under `anneal/theory/` fails closed.
            outside_lean = Path(tmp) / "outside_lean"
            outside_lean.mkdir()
            (outside_lean / "PureLift.lean").write_text("-- ok\n", encoding="utf-8")
            (theory_dir / "PureLift.lean").unlink()
            (theory_dir / "LinearArith.lean").unlink()
            theory_dir.rmdir()
            theory_dir.symlink_to(outside_lean)
            self.assert_fails_with(repo, "symlink forbidden: anneal/theory/Anneal")


    def test_cargo_anneal_companion_assets_match_anneal_skills(self) -> None:
        with tempfile.TemporaryDirectory() as tmp, patch.object(
            check_skills, "CARGO_ANNEAL_COMPANION_SKILLS", ("policy-review",)
        ):
            repo = self.build_fixture(Path(tmp))
            crate = repo / "anneal" / "trusted" / "cargo-anneal"
            assets = crate / "assets" / "skills"
            canonical = repo / "anneal" / "skills" / "policy-review" / "SKILL.md"
            asset = assets / "policy-review" / "SKILL.md"

            # The packaged copies are required only alongside the crate.
            check_skills.check_repository(repo)
            (crate / "Cargo.toml").write_text("[package]\n", encoding="utf-8")
            self.assert_fails_with(
                repo,
                "anneal/trusted/cargo-anneal/assets/skills: target does not exist",
            )

            asset.parent.mkdir(parents=True)
            asset.write_bytes(canonical.read_bytes())
            check_skills.check_repository(repo)

            # Drift in either direction fails closed.
            asset.write_bytes(canonical.read_bytes() + b"\nExtra.\n")
            self.assert_fails_with(repo, "stale packaged copy")
            asset.write_bytes(canonical.read_bytes())

            # Unlisted files and directories are rejected.
            stray = assets / "policy-review" / "NOTES.md"
            stray.write_text("# Notes\n", encoding="utf-8")
            self.assert_fails_with(repo, "unexpected entries")
            stray.unlink()
            (assets / "other").mkdir()
            self.assert_fails_with(repo, "unexpected entries")
            (assets / "other").rmdir()

            # A symlinked copy or a missing copy fails closed.
            asset.unlink()
            asset.symlink_to(canonical)
            self.assert_fails_with(repo, "symlink is forbidden")
            asset.unlink()
            asset.parent.rmdir()
            self.assert_fails_with(repo, "missing packaged copy")
            asset.parent.mkdir()
            asset.write_bytes(canonical.read_bytes())
            check_skills.check_repository(repo)

        # A packaged copy whose canonical source is gone fails closed.
        with tempfile.TemporaryDirectory() as tmp, patch.object(
            check_skills, "CARGO_ANNEAL_COMPANION_SKILLS", ("absent",)
        ):
            repo = self.build_fixture(Path(tmp))
            crate = repo / "anneal" / "trusted" / "cargo-anneal"
            (crate / "Cargo.toml").write_text("[package]\n", encoding="utf-8")
            write_skill_md(crate / "assets" / "skills" / "absent", "absent")
            self.assert_fails_with(
                repo, "anneal/skills/absent/SKILL.md: target does not exist"
            )

    def test_checks_toml_skills_check_inputs_cover_companion_assets(self) -> None:
        import tomllib

        checks_toml = REPO_ROOT / "ci" / "checks.toml"
        data = tomllib.loads(checks_toml.read_text(encoding="utf-8"))
        checks = {c["id"]: c for c in data.get("checks", [])}
        includes = {
            pat
            for inp in checks["skills-check"].get("inputs", [])
            if inp.get("kind") == "glob"
            for pat in inp.get("include", [])
        }
        crate = check_skills.CARGO_ANNEAL_CRATE_REL
        for required in (f"{crate}/Cargo.toml", f"{crate}/assets/**"):
            self.assertIn(required, includes)


if __name__ == "__main__":
    unittest.main()
