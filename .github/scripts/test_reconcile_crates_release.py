#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

from __future__ import annotations

import hashlib
import importlib.util
import json
import pathlib
import sys
import tempfile
import tomllib
import unittest
import urllib.parse
from collections.abc import Mapping, Sequence


sys.dont_write_bytecode = True
_SCRIPT = pathlib.Path(__file__).with_name("reconcile-crates-release.py")
_SPEC = importlib.util.spec_from_file_location(
    "reconcile_crates_release", _SCRIPT
)
assert _SPEC is not None and _SPEC.loader is not None
reconciler = importlib.util.module_from_spec(_SPEC)
sys.modules[_SPEC.name] = reconciler
_SPEC.loader.exec_module(reconciler)


_SHA = "0123456789abcdef0123456789abcdef01234567"
_OTHER_SHA = "fedcba9876543210fedcba9876543210fedcba98"
_TAG_OBJECT_ONE = "1111111111111111111111111111111111111111"
_TAG_OBJECT_TWO = "2222222222222222222222222222222222222222"
_CARGO_TOKEN = "cargo-secret-that-must-not-appear-in-arguments"
_GH_TOKEN = "github-secret-that-must-not-appear-in-arguments"


def _absent() -> reconciler.HttpResponse:
    return reconciler.HttpResponse(404, b'{"errors":[{"detail":"Not Found"}]}')


def _published(
    checksum: str, *, yanked: bool = False
) -> reconciler.HttpResponse:
    return reconciler.HttpResponse(
        200,
        json.dumps(
            {"version": {"checksum": checksum, "yanked": yanked}}
        ).encode(),
    )


class FakeRegistryHttp:
    """Returns a scripted sequence for each exact crate/version lookup."""

    def __init__(self) -> None:
        self._responses: dict[
            tuple[str, str], list[reconciler.HttpResponse]
        ] = {}
        self.calls: list[tuple[str, str]] = []

    def set(
        self,
        name: str,
        version: str,
        responses: Sequence[reconciler.HttpResponse],
    ) -> None:
        self._responses[(name, version)] = list(responses)

    def __call__(self, url: str) -> reconciler.HttpResponse:
        components = urllib.parse.urlsplit(url).path.rstrip("/").split("/")
        self.assert_path_shape(components, url)
        identity = (
            urllib.parse.unquote(components[-2]),
            urllib.parse.unquote(components[-1]),
        )
        self.calls.append(identity)
        if identity not in self._responses or not self._responses[identity]:
            raise AssertionError(f"unexpected registry lookup: {url}")
        responses = self._responses[identity]
        # Repeating the final state makes indefinite absence and stable
        # publication concise to express while preserving transition order.
        if len(responses) == 1:
            return responses[0]
        return responses.pop(0)

    @staticmethod
    def assert_path_shape(components: list[str], url: str) -> None:
        if len(components) < 4 or components[-3] != "crates":
            raise AssertionError(f"unexpected registry URL: {url}")


class FakeCommandRunner:
    """Models cargo publication and the small `gh` API used by the script."""

    def __init__(
        self,
        *,
        tag_object: Mapping[str, str] | None = None,
        annotated_objects: Mapping[str, Mapping[str, str]] | None = None,
        release_exists: bool = True,
        release_draft: bool = False,
        release_prerelease: bool = False,
    ) -> None:
        self.tag_object = dict(tag_object) if tag_object is not None else None
        self.annotated_objects = {
            sha: dict(value)
            for sha, value in (annotated_objects or {}).items()
        }
        self.release_exists = release_exists
        self.release_draft = release_draft
        self.release_prerelease = release_prerelease
        self.package_results: dict[str, reconciler.CommandResult] = {}
        self.repackaged_payloads: dict[str, bytes] = {}
        self.publish_results: dict[str, list[reconciler.CommandResult]] = {}
        self.create_result = reconciler.CommandResult(0)
        self.apply_create_on_failure = False
        self.calls: list[tuple[tuple[str, ...], dict[str, str]]] = []

    def __call__(
        self, arguments: Sequence[str], environment: Mapping[str, str]
    ) -> reconciler.CommandResult:
        args = tuple(arguments)
        self.calls.append((args, dict(environment)))
        if "publish" in args:
            package = args[args.index("--package") + 1]
            results = self.publish_results.get(package)
            if not results:
                return reconciler.CommandResult(0)
            if len(results) == 1:
                return results[0]
            return results.pop(0)

        if "package" in args:
            package = args[args.index("--package") + 1]
            result = self.package_results.get(
                package, reconciler.CommandResult(0)
            )
            if result.returncode != 0:
                return result
            manifest = pathlib.Path(args[args.index("--manifest-path") + 1])
            with manifest.open("rb") as manifest_file:
                version = tomllib.load(manifest_file)["package"]["version"]
            candidate_name = f"{package}-{version}.crate"
            candidate: pathlib.Path | None = None
            for ancestor in manifest.parents:
                path = ancestor / "target" / "package" / candidate_name
                if path.is_file():
                    candidate = path
                    break
            if candidate is None:
                raise AssertionError(
                    f"could not find prepared archive {candidate_name}"
                )
            payload = self.repackaged_payloads.get(
                package, candidate.read_bytes()
            )
            output_directory = (
                pathlib.Path(environment["CARGO_TARGET_DIR"]) / "package"
            )
            output_directory.mkdir(parents=True, exist_ok=True)
            (output_directory / candidate.name).write_bytes(payload)
            return result

        if len(args) >= 2 and args[0] == "fake-gh" and args[1] == "api":
            return self._api(args[-1])

        if args[:3] == ("fake-gh", "release", "create"):
            if (
                self.create_result.returncode == 0
                or self.apply_create_on_failure
            ):
                if "--target" in args:
                    target = args[args.index("--target") + 1]
                    self.tag_object = {"type": "commit", "sha": target}
                elif self.tag_object is None:
                    raise AssertionError(
                        "--verify-tag release creation needs an existing tag"
                    )
                self.release_exists = True
                self.release_draft = False
                self.release_prerelease = "--prerelease" in args
            return self.create_result

        raise AssertionError(f"unexpected command: {args!r}")

    def _api(self, endpoint: str) -> reconciler.CommandResult:
        if "/git/ref/tags/" in endpoint:
            if self.tag_object is None:
                return reconciler.CommandResult(
                    1, stderr="gh: Not Found (HTTP 404)"
                )
            return reconciler.CommandResult(
                0, stdout=json.dumps({"object": self.tag_object})
            )
        if "/git/tags/" in endpoint:
            sha = endpoint.rsplit("/", 1)[1]
            if sha not in self.annotated_objects:
                return reconciler.CommandResult(
                    1, stderr="gh: Not Found (HTTP 404)"
                )
            return reconciler.CommandResult(
                0,
                stdout=json.dumps(
                    {"object": self.annotated_objects[sha]}
                ),
            )
        if "/releases/tags/" in endpoint:
            if not self.release_exists:
                return reconciler.CommandResult(
                    1, stderr="gh: Not Found (HTTP 404)"
                )
            return reconciler.CommandResult(
                0,
                stdout=json.dumps(
                    {
                        "tag_name": "v1.2.3",
                        "draft": self.release_draft,
                        "prerelease": self.release_prerelease,
                    }
                ),
            )
        raise AssertionError(f"unexpected GitHub endpoint: {endpoint}")

    @property
    def publish_calls(
        self,
    ) -> list[tuple[tuple[str, ...], dict[str, str]]]:
        return [call for call in self.calls if "publish" in call[0]]

    @property
    def release_create_calls(
        self,
    ) -> list[tuple[tuple[str, ...], dict[str, str]]]:
        return [
            call
            for call in self.calls
            if call[0][:3] == ("fake-gh", "release", "create")
        ]

    @property
    def package_calls(
        self,
    ) -> list[tuple[tuple[str, ...], dict[str, str]]]:
        return [
            call
            for call in self.calls
            if "package" in call[0] and "publish" not in call[0]
        ]


class ReleaseReconcilerTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = pathlib.Path(temporary.name)
        self.http = FakeRegistryHttp()
        self.runner = FakeCommandRunner(
            tag_object={"type": "commit", "sha": _SHA},
            release_exists=True,
        )
        self.sleeps: list[float] = []
        self.reports: list[str] = []

    def package(
        self,
        name: str = "example",
        version: str = "1.2.3",
        *,
        payload: bytes | None = None,
    ) -> dict[str, str]:
        manifest_path = pathlib.Path("manifests") / name / "Cargo.toml"
        absolute_manifest = self.root / manifest_path
        absolute_manifest.parent.mkdir(parents=True, exist_ok=True)
        absolute_manifest.write_text(
            f'[package]\nname = "{name}"\nversion = "{version}"\n',
            encoding="utf-8",
        )

        archive_path = (
            pathlib.Path("target") / "package" / f"{name}-{version}.crate"
        )
        absolute_archive = self.root / archive_path
        absolute_archive.parent.mkdir(parents=True, exist_ok=True)
        archive_payload = payload or f"archive:{name}:{version}".encode()
        absolute_archive.write_bytes(archive_payload)
        return {
            "name": name,
            "version": version,
            "manifest_path": str(manifest_path),
            "archive_path": str(archive_path),
            "sha256": hashlib.sha256(archive_payload).hexdigest(),
        }

    def plan(
        self,
        packages: Sequence[Mapping[str, str]],
        **overrides: object,
    ) -> reconciler.ReleasePlan:
        value: dict[str, object] = {
            "schema": 1,
            "repository": "google/zerocopy",
            "tag": "v1.2.3",
            "sha": _SHA,
            "workflow": "release.yml",
            "environment": "release",
            "prerelease": False,
            "cargo_command": ["fake-cargo", "+stable"],
            "gh_command": ["fake-gh"],
            "packages": list(packages),
        }
        value.update(overrides)
        plan_path = self.root / "release-plan.json"
        plan_path.write_text(json.dumps(value), encoding="utf-8")
        return reconciler.ReleasePlan.from_file(plan_path, root=self.root)

    def reconcile(
        self,
        plan: reconciler.ReleasePlan,
        *,
        environment: Mapping[str, str] | None = None,
        poll_delays: Sequence[float] = (0.125, 0.25),
    ) -> None:
        reconciler.ReleaseReconciler(
            plan,
            http_get=self.http,
            command_runner=self.runner,
            sleep=self.sleeps.append,
            environment=environment
            or {
                "CARGO_REGISTRY_TOKEN": _CARGO_TOKEN,
                "GH_TOKEN": _GH_TOKEN,
                "ACTIONS_ID_TOKEN_REQUEST_TOKEN": "oidc-secret",
            },
            report=self.reports.append,
            registry_api="https://registry.invalid/api/v1",
            poll_delays=poll_delays,
        ).run()

    def test_matching_versions_and_existing_release_are_no_ops(self) -> None:
        derive = self.package("example-derive")
        main = self.package("example")
        plan = self.plan([derive, main])
        self.http.set(
            "example-derive",
            "1.2.3",
            [_published(derive["sha256"])],
        )
        self.http.set(
            "example", "1.2.3", [_published(main["sha256"])]
        )

        self.reconcile(plan)

        self.assertEqual(self.runner.publish_calls, [])
        self.assertEqual(self.runner.release_create_calls, [])
        self.assertEqual(
            self.http.calls,
            [("example-derive", "1.2.3"), ("example", "1.2.3")],
        )
        self.assertTrue(
            any("already match" in report for report in self.reports)
        )

    def test_absent_packages_publish_in_plan_order_without_verification(
        self,
    ) -> None:
        derive = self.package("example-derive")
        main = self.package("example")
        plan = self.plan([derive, main])
        self.http.set(
            "example-derive",
            "1.2.3",
            [_absent(), _published(derive["sha256"])],
        )
        self.http.set(
            "example",
            "1.2.3",
            [_absent(), _published(main["sha256"])],
        )

        self.reconcile(plan)

        calls = self.runner.publish_calls
        self.assertEqual(
            [args[args.index("--package") + 1] for args, _ in calls],
            ["example-derive", "example"],
        )
        for args, environment in calls:
            self.assertEqual(args[:3], ("fake-cargo", "+stable", "publish"))
            self.assertIn("--locked", args)
            self.assertIn("--no-verify", args)
            self.assertNotIn("--allow-dirty", args)
            self.assertIn("--manifest-path", args)
            self.assertEqual(environment["CARGO_REGISTRY_TOKEN"], _CARGO_TOKEN)
            self.assertNotIn("GH_TOKEN", environment)
            self.assertNotIn("ACTIONS_ID_TOKEN_REQUEST_TOKEN", environment)
            self.assertNotIn(_CARGO_TOKEN, args)
            self.assertNotIn(_GH_TOKEN, args)
        self.assertNotIn("--config", calls[0][0])
        publish_patch = calls[1][0][calls[1][0].index("--config") + 1]
        self.assertIn("patch.crates-io.example-derive.path=", publish_patch)
        self.assertEqual(len(self.runner.package_calls), 2)
        for args, environment in self.runner.package_calls:
            self.assertIn("--locked", args)
            self.assertFalse(
                any("TOKEN" in name.upper() for name in environment)
            )
            self.assertIn("CARGO_TARGET_DIR", environment)
        derive_package_args = self.runner.package_calls[0][0]
        main_package_args = self.runner.package_calls[1][0]
        self.assertNotIn("--config", derive_package_args)
        patch = main_package_args[main_package_args.index("--config") + 1]
        self.assertIn("patch.crates-io.example-derive.path=", patch)
        self.assertEqual(self.sleeps, [])

    def test_existing_checksum_mismatch_is_rejected(self) -> None:
        package = self.package()
        plan = self.plan([package])
        wrong_checksum = "f" * 64
        self.http.set(
            "example", "1.2.3", [_published(wrong_checksum)]
        )

        with self.assertRaisesRegex(
            reconciler.ReleaseError, "checksum.*this release expects"
        ):
            self.reconcile(plan)

        self.assertEqual(self.runner.publish_calls, [])
        self.assertEqual(self.runner.release_create_calls, [])

    def test_existing_yanked_version_is_rejected(self) -> None:
        package = self.package()
        plan = self.plan([package])
        self.http.set(
            "example",
            "1.2.3",
            [_published(package["sha256"], yanked=True)],
        )

        with self.assertRaisesRegex(reconciler.ReleaseError, "is yanked"):
            self.reconcile(plan)

        self.assertEqual(self.runner.publish_calls, [])
        self.assertEqual(self.runner.release_create_calls, [])

    def test_failed_publish_is_accepted_after_matching_version_appears(
        self,
    ) -> None:
        package = self.package()
        plan = self.plan([package])
        self.http.set(
            "example",
            "1.2.3",
            [
                _absent(),  # Initial desired-state query.
                _absent(),  # Immediate response-loss recovery query.
                _absent(),  # First bounded-poll query.
                _published(package["sha256"]),
            ],
        )
        self.runner.publish_results["example"] = [
            reconciler.CommandResult(
                1, stderr="connection closed before response arrived"
            )
        ]

        self.reconcile(plan)

        self.assertEqual(self.sleeps, [0.125])
        self.assertTrue(
            any("appeared after cargo's failure" in value for value in self.reports)
        )

    def test_registry_polling_has_a_bounded_timeout(self) -> None:
        package = self.package()
        plan = self.plan([package])
        self.http.set("example", "1.2.3", [_absent()])

        with self.assertRaisesRegex(
            reconciler.RegistryTimeout,
            "did not appear on crates.io after 0.375 seconds",
        ):
            self.reconcile(plan)

        self.assertEqual(self.sleeps, [0.125, 0.25])
        self.assertEqual(self.runner.release_create_calls, [])

    def test_publish_403_names_every_trusted_publisher_coordinate(
        self,
    ) -> None:
        package = self.package("example-derive")
        plan = self.plan([package])
        self.http.set("example-derive", "1.2.3", [_absent()])
        self.runner.publish_results["example-derive"] = [
            reconciler.CommandResult(
                1,
                stderr=(
                    "HTTP 403 Forbidden: The provided access token is not "
                    f"valid for crate `example-derive`: {_CARGO_TOKEN}"
                ),
            )
        ]

        with self.assertRaises(reconciler.ReleaseError) as raised:
            self.reconcile(plan)

        message = str(raised.exception)
        for expected in (
            "Owner: google",
            "Repository: zerocopy",
            "Workflow: release.yml",
            "Environment: release",
            "Crate: example-derive",
        ):
            with self.subTest(expected=expected):
                self.assertIn(expected, message)
        self.assertNotIn(_CARGO_TOKEN, message)
        self.assertEqual(self.sleeps, [])

    def test_correct_annotated_tag_is_peeled_to_its_commit(self) -> None:
        package = self.package()
        plan = self.plan([package])
        self.http.set(
            "example", "1.2.3", [_published(package["sha256"])]
        )
        self.runner = FakeCommandRunner(
            tag_object={"type": "tag", "sha": _TAG_OBJECT_ONE},
            annotated_objects={
                _TAG_OBJECT_ONE: {"type": "tag", "sha": _TAG_OBJECT_TWO},
                _TAG_OBJECT_TWO: {"type": "commit", "sha": _SHA},
            },
            release_exists=True,
        )

        self.reconcile(plan)

        api_endpoints = [
            args[-1]
            for args, _ in self.runner.calls
            if args[:2] == ("fake-gh", "api")
        ]
        self.assertTrue(
            any(endpoint.endswith(_TAG_OBJECT_ONE) for endpoint in api_endpoints)
        )
        self.assertTrue(
            any(endpoint.endswith(_TAG_OBJECT_TWO) for endpoint in api_endpoints)
        )
        self.assertEqual(self.runner.release_create_calls, [])

    def test_wrong_existing_tag_is_rejected_without_creating_release(
        self,
    ) -> None:
        package = self.package()
        plan = self.plan([package])
        self.http.set(
            "example", "1.2.3", [_published(package["sha256"])]
        )
        self.runner = FakeCommandRunner(
            tag_object={"type": "commit", "sha": _OTHER_SHA},
            release_exists=False,
        )

        with self.assertRaisesRegex(
            reconciler.ReleaseError, "peels to.*refusing to move"
        ):
            self.reconcile(plan)

        self.assertEqual(self.runner.release_create_calls, [])

    def test_missing_tag_and_release_are_created_only_after_packages(
        self,
    ) -> None:
        package = self.package()
        plan = self.plan([package])
        self.http.set(
            "example",
            "1.2.3",
            [_absent(), _published(package["sha256"])],
        )
        self.runner = FakeCommandRunner(
            tag_object=None, release_exists=False
        )

        self.reconcile(plan)

        create = self.runner.release_create_calls
        self.assertEqual(len(create), 1)
        create_args, create_environment = create[0]
        self.assertIn("--target", create_args)
        self.assertEqual(
            create_args[create_args.index("--target") + 1], _SHA
        )
        self.assertNotIn("--verify-tag", create_args)
        self.assertNotIn("--latest", create_args)
        self.assertEqual(create_environment["GH_TOKEN"], _GH_TOKEN)
        self.assertNotIn("CARGO_REGISTRY_TOKEN", create_environment)
        self.assertNotIn("ACTIONS_ID_TOKEN_REQUEST_TOKEN", create_environment)
        self.assertNotIn(_GH_TOKEN, create_args)

        publish_index = next(
            index
            for index, (args, _) in enumerate(self.runner.calls)
            if "publish" in args
        )
        create_index = next(
            index
            for index, (args, _) in enumerate(self.runner.calls)
            if args[:3] == ("fake-gh", "release", "create")
        )
        self.assertLess(publish_index, create_index)

    def test_missing_release_is_created_from_verified_existing_tag(self) -> None:
        package = self.package()
        plan = self.plan([package])
        self.http.set(
            "example", "1.2.3", [_published(package["sha256"])]
        )
        self.runner = FakeCommandRunner(
            tag_object={"type": "commit", "sha": _SHA},
            release_exists=False,
        )

        self.reconcile(plan)

        create_args, _ = self.runner.release_create_calls[0]
        self.assertIn("--verify-tag", create_args)
        self.assertNotIn("--target", create_args)

    def test_existing_release_without_tag_is_rejected(self) -> None:
        package = self.package()
        plan = self.plan([package])
        self.http.set(
            "example", "1.2.3", [_published(package["sha256"])]
        )
        self.runner = FakeCommandRunner(
            tag_object=None, release_exists=True
        )

        with self.assertRaisesRegex(
            reconciler.ReleaseError, "release.*exists.*git tag.*does not"
        ):
            self.reconcile(plan)

        self.assertEqual(self.runner.release_create_calls, [])

    def test_draft_release_is_not_accepted_as_complete(self) -> None:
        package = self.package()
        plan = self.plan([package])
        self.http.set(
            "example", "1.2.3", [_published(package["sha256"])]
        )
        self.runner = FakeCommandRunner(
            tag_object={"type": "commit", "sha": _SHA},
            release_exists=True,
            release_draft=True,
        )

        with self.assertRaisesRegex(reconciler.ReleaseError, "still a draft"):
            self.reconcile(plan)

        self.assertEqual(self.runner.release_create_calls, [])

    def test_release_prerelease_state_must_match_plan(self) -> None:
        package = self.package()
        plan = self.plan([package], prerelease=True)
        self.http.set(
            "example", "1.2.3", [_published(package["sha256"])]
        )
        self.runner = FakeCommandRunner(
            tag_object={"type": "commit", "sha": _SHA},
            release_exists=True,
            release_prerelease=False,
        )

        with self.assertRaisesRegex(
            reconciler.ReleaseError,
            "prerelease=False, expected True",
        ):
            self.reconcile(plan)

        self.assertEqual(self.runner.release_create_calls, [])

    def test_failed_gh_command_is_accepted_if_release_appeared(self) -> None:
        package = self.package()
        plan = self.plan([package])
        self.http.set(
            "example", "1.2.3", [_published(package["sha256"])]
        )
        self.runner = FakeCommandRunner(
            tag_object=None, release_exists=False
        )
        self.runner.create_result = reconciler.CommandResult(
            1, stderr="connection lost"
        )
        self.runner.apply_create_on_failure = True

        self.reconcile(plan)

        self.assertTrue(
            any("despite gh's failure" in value for value in self.reports)
        )

    def test_non_reproducible_packaging_prevents_registry_access(self) -> None:
        package = self.package()
        plan = self.plan([package])
        self.runner.repackaged_payloads["example"] = b"different packaging"

        with self.assertRaisesRegex(
            reconciler.ReleaseError, "refusing to publish non-reproducible"
        ):
            self.reconcile(plan)

        self.assertEqual(self.http.calls, [])
        self.assertEqual(self.runner.publish_calls, [])
        self.assertEqual(self.runner.release_create_calls, [])

    def test_archive_checksum_failure_prevents_all_remote_operations(
        self,
    ) -> None:
        package = self.package()
        plan = self.plan([package])
        archive = self.root / package["archive_path"]
        archive.write_bytes(b"changed after the plan was produced")

        with self.assertRaisesRegex(
            reconciler.ReleaseError, "archive.*SHA-256"
        ):
            self.reconcile(plan)

        self.assertEqual(self.http.calls, [])
        self.assertEqual(self.runner.calls, [])

    def test_manifest_plan_mismatch_prevents_all_remote_operations(self) -> None:
        package = self.package()
        plan = self.plan([package])
        manifest = self.root / package["manifest_path"]
        manifest.write_text(
            '[package]\nname = "example"\nversion = "9.9.9"\n',
            encoding="utf-8",
        )

        with self.assertRaisesRegex(
            reconciler.ReleaseError, "describes example 9.9.9"
        ):
            self.reconcile(plan)

        self.assertEqual(self.http.calls, [])
        self.assertEqual(self.runner.calls, [])

    def test_plan_paths_cannot_escape_release_root(self) -> None:
        package = self.package()
        package["manifest_path"] = "../outside/Cargo.toml"

        with self.assertRaisesRegex(reconciler.PlanError, "escapes --root"):
            self.plan([package])


if __name__ == "__main__":
    unittest.main()
