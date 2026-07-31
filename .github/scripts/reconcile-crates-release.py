#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Idempotently reconcile a crates.io and GitHub release.

Publishing a release is an irreversible, multi-system transaction. A runner
can disappear after crates.io accepted an upload, crates.io can take time to
expose an accepted version, and a later crate in the release can fail after an
earlier one was published. Retrying a sequence of imperative publish commands
does not handle those cases safely. This script instead compares each desired
object with remote state before deciding whether it needs to create anything.

The input is a versioned JSON plan. Package order is significant and must be
dependency order. Paths are absolute or relative to ``--root`` (the current
directory by default):

{
  "schema": 1,
  "repository": "google/zerocopy",
  "tag": "v0.8.56",
  "sha": "0123456789abcdef0123456789abcdef01234567",
  "workflow": "release.yml",
  "environment": "release",
  "prerelease": false,
  "cargo_command": ["./cargo.sh", "+stable"],
  "packages": [
    {
      "name": "zerocopy-derive",
      "version": "0.8.56",
      "manifest_path": "zerocopy-derive/Cargo.toml",
      "archive_path": "target/package/zerocopy-derive-0.8.56.crate",
      "sha256": "...64 lowercase hexadecimal characters..."
    }
  ]
}

The caller must put the crates.io credential in ``CARGO_REGISTRY_TOKEN`` and
the GitHub credential in ``GH_TOKEN``. Credentials are inherited by child
processes and are never placed in command-line arguments. ``cargo_command`` is
only the command prefix; this script appends a ``cargo publish --no-verify``
invocation for each absent package. ``gh_command`` may optionally override the
default ``["gh"]`` command prefix.

The expected archive is deliberately part of the plan even though Cargo does
not provide a command for uploading an already-built archive. Before making
any changes, the script verifies every archive's SHA-256 digest and every
source manifest's package name and version. It then packages each manifest
again in an isolated temporary target directory and requires the new archive
to have the same digest. Only then can ``cargo publish`` repackage and upload
it. After a publish, the script verifies that crates.io's checksum is the
expected archive checksum. Thus a rerun can prove that an already-published
version is precisely the artifact this release intended; it never treats
"version already exists" as success by itself.

HTTP, subprocess execution, sleeping, environment access, and reporting are
injected into ``ReleaseReconciler``. Unit tests can therefore exercise all
state transitions without network access, credentials, or external commands.
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile
import time
import tomllib
import urllib.error
import urllib.parse
import urllib.request
from collections.abc import Callable, Mapping, Sequence
from typing import Any


_CRATES_IO_API = "https://crates.io/api/v1"
_DEFAULT_POLL_DELAYS = (1.0, 2.0, 4.0, 8.0, 15.0, 30.0)
_HEX_SHA256 = re.compile(r"^[0-9a-f]{64}$")
_GIT_SHA1 = re.compile(r"^[0-9a-fA-F]{40}$")
_REPOSITORY = re.compile(
    r"^[A-Za-z0-9](?:[A-Za-z0-9_.-]*[A-Za-z0-9])?/"
    r"[A-Za-z0-9](?:[A-Za-z0-9_.-]*[A-Za-z0-9])?$"
)


class ReleaseError(RuntimeError):
    """A safe, actionable release failure."""


class PlanError(ReleaseError):
    """A malformed or internally inconsistent release plan."""


class RegistryTimeout(ReleaseError):
    """A successful-looking publish which never became observable."""


@dataclasses.dataclass(frozen=True)
class HttpResponse:
    status: int
    body: bytes


@dataclasses.dataclass(frozen=True)
class CommandResult:
    returncode: int
    stdout: str = ""
    stderr: str = ""


@dataclasses.dataclass(frozen=True)
class PackagePlan:
    name: str
    version: str
    manifest_path: pathlib.Path
    archive_path: pathlib.Path
    sha256: str


@dataclasses.dataclass(frozen=True)
class ReleasePlan:
    repository: str
    tag: str
    sha: str
    workflow: str
    environment: str
    prerelease: bool
    cargo_command: tuple[str, ...]
    gh_command: tuple[str, ...]
    packages: tuple[PackagePlan, ...]

    @property
    def owner(self) -> str:
        return self.repository.split("/", 1)[0]

    @property
    def repository_name(self) -> str:
        return self.repository.split("/", 1)[1]

    @classmethod
    def from_file(
        cls, path: pathlib.Path, *, root: pathlib.Path
    ) -> ReleasePlan:
        try:
            with path.open("rb") as plan_file:
                value = json.load(plan_file)
        except (OSError, json.JSONDecodeError) as error:
            raise PlanError(f"could not read release plan {path}: {error}") from error
        return cls.from_value(value, root=root)

    @classmethod
    def from_value(
        cls, value: object, *, root: pathlib.Path
    ) -> ReleasePlan:
        plan = _object(value, "release plan")
        _reject_unknown(
            plan,
            {
                "schema",
                "repository",
                "tag",
                "sha",
                "workflow",
                "environment",
                "prerelease",
                "cargo_command",
                "gh_command",
                "packages",
            },
            "release plan",
        )

        schema = plan.get("schema")
        if schema != 1 or isinstance(schema, bool):
            raise PlanError(
                f"release plan schema must be the integer 1, not {schema!r}"
            )

        repository = _string(plan, "repository", "release plan")
        if not _REPOSITORY.fullmatch(repository):
            raise PlanError(
                "release plan repository must have the form `owner/name`"
            )

        tag = _string(plan, "tag", "release plan")
        _reject_control_characters(tag, "release plan tag")
        sha = _string(plan, "sha", "release plan")
        if not _GIT_SHA1.fullmatch(sha):
            raise PlanError("release plan sha must be a full 40-digit Git SHA")

        workflow = _string(plan, "workflow", "release plan")
        if pathlib.PurePath(workflow).name != workflow or not workflow.endswith(
            (".yml", ".yaml")
        ):
            raise PlanError(
                "release plan workflow must be a workflow filename such as "
                "`release.yml`"
            )
        environment = _string(plan, "environment", "release plan")
        _reject_control_characters(environment, "release plan environment")

        prerelease_value = plan.get("prerelease", False)
        if not isinstance(prerelease_value, bool):
            raise PlanError("release plan prerelease must be a boolean")

        cargo_command = _command(plan, "cargo_command", required=True)
        gh_command = _command(plan, "gh_command", required=False) or ("gh",)

        raw_packages = plan.get("packages")
        if not isinstance(raw_packages, list) or not raw_packages:
            raise PlanError("release plan packages must be a non-empty array")

        resolved_root = root.resolve()
        packages: list[PackagePlan] = []
        identities: set[tuple[str, str]] = set()
        for index, raw_package in enumerate(raw_packages):
            context = f"release plan packages[{index}]"
            package = _object(raw_package, context)
            _reject_unknown(
                package,
                {
                    "name",
                    "version",
                    "manifest_path",
                    "archive_path",
                    "sha256",
                },
                context,
            )
            name = _string(package, "name", context)
            version = _string(package, "version", context)
            manifest_path = _plan_path(
                _string(package, "manifest_path", context), resolved_root
            )
            archive_path = _plan_path(
                _string(package, "archive_path", context), resolved_root
            )
            sha256 = _string(package, "sha256", context).lower()
            if not _HEX_SHA256.fullmatch(sha256):
                raise PlanError(f"{context}.sha256 must be a SHA-256 digest")
            if archive_path.name != f"{name}-{version}.crate":
                raise PlanError(
                    f"{context}.archive_path must end in "
                    f"{name}-{version}.crate"
                )
            identity = (name, version)
            if identity in identities:
                raise PlanError(
                    f"release plan contains {name} {version} more than once"
                )
            identities.add(identity)
            packages.append(
                PackagePlan(
                    name=name,
                    version=version,
                    manifest_path=manifest_path,
                    archive_path=archive_path,
                    sha256=sha256,
                )
            )

        return cls(
            repository=repository,
            tag=tag,
            sha=sha.lower(),
            workflow=workflow,
            environment=environment,
            prerelease=prerelease_value,
            cargo_command=cargo_command,
            gh_command=gh_command,
            packages=tuple(packages),
        )


@dataclasses.dataclass(frozen=True)
class RegistryVersion:
    checksum: str
    yanked: bool


HttpGetter = Callable[[str], HttpResponse]
CommandRunner = Callable[[Sequence[str], Mapping[str, str]], CommandResult]
Sleeper = Callable[[float], None]
Reporter = Callable[[str], None]


def _object(value: object, context: str) -> dict[str, Any]:
    if not isinstance(value, dict) or not all(
        isinstance(key, str) for key in value
    ):
        raise PlanError(f"{context} must be a JSON object with string keys")
    return value


def _reject_unknown(
    value: Mapping[str, object], allowed: set[str], context: str
) -> None:
    unknown = sorted(set(value) - allowed)
    if unknown:
        raise PlanError(
            f"{context} has unknown field(s): {', '.join(unknown)}"
        )


def _string(value: Mapping[str, object], key: str, context: str) -> str:
    result = value.get(key)
    if not isinstance(result, str) or not result:
        raise PlanError(f"{context}.{key} must be a non-empty string")
    _reject_control_characters(result, f"{context}.{key}")
    return result


def _reject_control_characters(value: str, context: str) -> None:
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise PlanError(f"{context} must not contain control characters")


def _command(
    value: Mapping[str, object], key: str, *, required: bool
) -> tuple[str, ...] | None:
    raw_command = value.get(key)
    if raw_command is None and not required:
        return None
    if (
        not isinstance(raw_command, list)
        or not raw_command
        or not all(isinstance(argument, str) and argument for argument in raw_command)
    ):
        raise PlanError(
            f"release plan {key} must be a non-empty array of strings"
        )
    for argument in raw_command:
        _reject_control_characters(argument, f"release plan {key} argument")
    return tuple(raw_command)


def _plan_path(value: str, root: pathlib.Path) -> pathlib.Path:
    path = pathlib.Path(value)
    if not path.is_absolute():
        path = root / path
    resolved = path.resolve()
    try:
        resolved.relative_to(root)
    except ValueError as error:
        raise PlanError(
            f"release plan path {value!r} escapes --root {root}"
        ) from error
    return resolved


def _default_http_get(url: str) -> HttpResponse:
    request = urllib.request.Request(
        url,
        headers={
            # crates.io requires clients to identify themselves. Keep this URL
            # useful if registry operators need to contact the project.
            "User-Agent": (
                "zerocopy-release-reconciler/1 "
                "(+https://github.com/google/zerocopy)"
            )
        },
        method="GET",
    )
    try:
        with urllib.request.urlopen(request, timeout=30) as response:
            return HttpResponse(response.status, response.read())
    except urllib.error.HTTPError as error:
        return HttpResponse(error.code, error.read())
    except urllib.error.URLError as error:
        raise ReleaseError(f"GET {url} failed: {error.reason}") from error


def _default_command_runner(
    arguments: Sequence[str], environment: Mapping[str, str]
) -> CommandResult:
    try:
        completed = subprocess.run(
            list(arguments),
            check=False,
            capture_output=True,
            env=dict(environment),
            text=True,
        )
    except OSError as error:
        raise ReleaseError(
            f"could not execute {arguments[0]!r}: {error}"
        ) from error
    return CommandResult(
        completed.returncode, completed.stdout, completed.stderr
    )


class CratesIoClient:
    def __init__(
        self,
        http_get: HttpGetter,
        *,
        api_base: str = _CRATES_IO_API,
    ) -> None:
        self._http_get = http_get
        self._api_base = api_base.rstrip("/")

    def get_version(self, package: PackagePlan) -> RegistryVersion | None:
        name = urllib.parse.quote(package.name, safe="")
        version = urllib.parse.quote(package.version, safe="")
        url = f"{self._api_base}/crates/{name}/{version}"
        response = self._http_get(url)
        if response.status == 404:
            return None
        if response.status != 200:
            detail = response.body.decode("utf-8", errors="replace").strip()
            if detail:
                detail = f": {detail[:500]}"
            raise ReleaseError(
                f"crates.io returned HTTP {response.status} for "
                f"{package.name} {package.version}{detail}"
            )
        try:
            payload = json.loads(response.body)
            version_value = payload["version"]
            checksum = version_value["checksum"]
            yanked = version_value["yanked"]
        except (KeyError, TypeError, json.JSONDecodeError) as error:
            raise ReleaseError(
                f"crates.io returned an invalid response for "
                f"{package.name} {package.version}"
            ) from error
        if not isinstance(checksum, str) or not _HEX_SHA256.fullmatch(
            checksum.lower()
        ):
            raise ReleaseError(
                f"crates.io returned an invalid checksum for "
                f"{package.name} {package.version}"
            )
        if not isinstance(yanked, bool):
            raise ReleaseError(
                f"crates.io returned an invalid yanked value for "
                f"{package.name} {package.version}"
            )
        return RegistryVersion(checksum.lower(), yanked)


class GitHubClient:
    """The small, testable subset of ``gh`` needed for release state."""

    def __init__(
        self,
        plan: ReleasePlan,
        command_runner: CommandRunner,
        environment: Mapping[str, str],
    ) -> None:
        self._plan = plan
        self._command_runner = command_runner
        self._environment = environment

    def _run(self, arguments: Sequence[str]) -> CommandResult:
        return self._command_runner(
            [*self._plan.gh_command, *arguments], self._environment
        )

    def _get_json(self, endpoint: str) -> dict[str, Any] | None:
        result = self._run(("api", "--method", "GET", endpoint))
        if result.returncode != 0:
            diagnostic = f"{result.stdout}\n{result.stderr}".lower()
            if "http 404" in diagnostic or "not found" in diagnostic:
                return None
            raise ReleaseError(
                f"GitHub API request for {endpoint} failed: "
                f"{_redact_diagnostic(result.stderr, self._environment)}"
            )
        try:
            value = json.loads(result.stdout)
        except json.JSONDecodeError as error:
            raise ReleaseError(
                f"GitHub API returned invalid JSON for {endpoint}"
            ) from error
        if not isinstance(value, dict):
            raise ReleaseError(
                f"GitHub API returned a non-object for {endpoint}"
            )
        return value

    def tag_target(self) -> str | None:
        tag = urllib.parse.quote(self._plan.tag, safe="")
        ref_endpoint = (
            f"repos/{self._plan.repository}/git/ref/tags/{tag}"
        )
        ref = self._get_json(ref_endpoint)
        if ref is None:
            return None
        object_type, sha = _github_object(ref, ref_endpoint)

        # Annotated tags may point to another annotated tag. Peel the chain and
        # compare the final commit, not the tag object's own SHA.
        seen: set[str] = set()
        for _ in range(16):
            if object_type == "commit":
                return sha.lower()
            if object_type != "tag":
                raise ReleaseError(
                    f"GitHub tag {self._plan.tag} points to unsupported "
                    f"object type {object_type!r}"
                )
            if sha in seen:
                raise ReleaseError(
                    f"GitHub tag {self._plan.tag} contains a tag-object cycle"
                )
            seen.add(sha)
            endpoint = f"repos/{self._plan.repository}/git/tags/{sha}"
            tag_object = self._get_json(endpoint)
            if tag_object is None:
                raise ReleaseError(
                    f"GitHub tag object {sha} disappeared while peeling "
                    f"{self._plan.tag}"
                )
            object_type, sha = _github_object(tag_object, endpoint)
        raise ReleaseError(
            f"GitHub tag {self._plan.tag} has more than 16 nested tag objects"
        )

    def release_exists(self) -> bool:
        tag = urllib.parse.quote(self._plan.tag, safe="")
        endpoint = f"repos/{self._plan.repository}/releases/tags/{tag}"
        release = self._get_json(endpoint)
        if release is None:
            return False
        tag_name = release.get("tag_name")
        if tag_name != self._plan.tag:
            raise ReleaseError(
                f"GitHub returned release tag {tag_name!r} while looking up "
                f"{self._plan.tag!r}"
            )
        draft = release.get("draft")
        prerelease = release.get("prerelease")
        if not isinstance(draft, bool) or not isinstance(prerelease, bool):
            raise ReleaseError(
                f"GitHub release {self._plan.tag} has invalid draft or "
                "prerelease metadata"
            )
        if draft:
            raise ReleaseError(
                f"GitHub release {self._plan.tag} is still a draft"
            )
        if prerelease != self._plan.prerelease:
            raise ReleaseError(
                f"GitHub release {self._plan.tag} has prerelease="
                f"{prerelease}, expected {self._plan.prerelease}"
            )
        return True

    def create_release(self, *, tag_exists: bool) -> CommandResult:
        arguments = [
            "release",
            "create",
            self._plan.tag,
            "--repo",
            self._plan.repository,
            "--generate-notes",
        ]
        if tag_exists:
            arguments.append("--verify-tag")
        else:
            arguments.extend(("--target", self._plan.sha))
        if self._plan.prerelease:
            arguments.append("--prerelease")
        # Do not force stable releases to be Latest. GitHub's default policy
        # accounts for semantic version and creation date, while `--latest`
        # would let a late approval for an older version demote a newer one.
        return self._run(arguments)


def _github_object(
    value: Mapping[str, object], endpoint: str
) -> tuple[str, str]:
    object_value = value.get("object")
    if not isinstance(object_value, dict):
        raise ReleaseError(f"GitHub response for {endpoint} has no object")
    object_type = object_value.get("type")
    sha = object_value.get("sha")
    if not isinstance(object_type, str) or not isinstance(sha, str) or not sha:
        raise ReleaseError(
            f"GitHub response for {endpoint} has an invalid object"
        )
    return object_type, sha


class ReleaseReconciler:
    def __init__(
        self,
        plan: ReleasePlan,
        *,
        http_get: HttpGetter = _default_http_get,
        command_runner: CommandRunner = _default_command_runner,
        sleep: Sleeper = time.sleep,
        environment: Mapping[str, str] = os.environ,
        report: Reporter = print,
        registry_api: str = _CRATES_IO_API,
        poll_delays: Sequence[float] = _DEFAULT_POLL_DELAYS,
    ) -> None:
        if any(delay < 0 for delay in poll_delays):
            raise ValueError("poll delays must not be negative")
        self._plan = plan
        self._command_runner = command_runner
        # Take a copy so a caller cannot change credential scope midway
        # through a reconciliation.
        self._environment = dict(environment)
        self._cargo_environment = self._environment_with_tokens(
            {"CARGO_REGISTRY_TOKEN"}
        )
        github_environment = self._environment_with_tokens({"GH_TOKEN"})
        self._sleep = sleep
        self._report = report
        self._poll_delays = tuple(float(delay) for delay in poll_delays)
        self._registry = CratesIoClient(http_get, api_base=registry_api)
        self._github = GitHubClient(
            plan, command_runner, github_environment
        )

    def _environment_with_tokens(
        self, permitted_tokens: set[str]
    ) -> dict[str, str]:
        return {
            name: value
            for name, value in self._environment.items()
            if "TOKEN" not in name.upper() or name in permitted_tokens
        }

    def run(self) -> None:
        self._preflight()
        for index, package in enumerate(self._plan.packages):
            self._reconcile_package(package, self._plan.packages[:index])
        # Tags and releases are created only after every package is known to
        # match. A GitHub release can therefore never advertise a partial
        # crates.io release.
        self._reconcile_github_release()

    def _preflight(self) -> None:
        if not self._environment.get("GH_TOKEN"):
            raise ReleaseError(
                "GH_TOKEN must be set in the environment; the GitHub token "
                "must not be passed in a command-line argument"
            )
        for package in self._plan.packages:
            self._verify_manifest(package)
            self._verify_archive(package)
        for index, package in enumerate(self._plan.packages):
            self._verify_repackaged_archive(
                package, self._plan.packages[:index]
            )
        self._report("Validated all release manifests and archives.")

    def _verify_manifest(self, package: PackagePlan) -> None:
        try:
            with package.manifest_path.open("rb") as manifest_file:
                manifest = tomllib.load(manifest_file)
            metadata = manifest["package"]
            name = metadata["name"]
            version = metadata["version"]
        except (OSError, KeyError, TypeError, tomllib.TOMLDecodeError) as error:
            raise ReleaseError(
                f"could not read package metadata from "
                f"{package.manifest_path}: {error}"
            ) from error
        # These release manifests currently use literal versions. If that
        # changes (for example to `version.workspace = true`), fail loudly
        # instead of guessing how the new source of truth relates to the plan.
        if not isinstance(name, str) or not isinstance(version, str):
            raise ReleaseError(
                f"{package.manifest_path} must have literal package.name and "
                "package.version strings; update the release reconciler if "
                "the manifests begin inheriting either field"
            )
        if name != package.name or version != package.version:
            raise ReleaseError(
                f"{package.manifest_path} describes {name} {version}, but the "
                f"release plan expects {package.name} {package.version}"
            )

    def _verify_archive(self, package: PackagePlan) -> None:
        actual = _sha256_file(package.archive_path, "release archive")
        if actual != package.sha256:
            raise ReleaseError(
                f"release archive {package.archive_path} has SHA-256 "
                f"{actual}, but the plan expects {package.sha256}"
            )

    def _verify_repackaged_archive(
        self,
        package: PackagePlan,
        prior_packages: Sequence[PackagePlan],
    ) -> None:
        # Cargo cannot publish a prebuilt `.crate`; `cargo publish` always
        # packages the source tree itself. Reproduce that packaging step in an
        # isolated target directory first. This couples the checksum produced
        # by the unprivileged preparation job to the exact source checkout used
        # by the privileged publishing job without overwriting the reference
        # archive downloaded from the former.
        with tempfile.TemporaryDirectory(
            prefix="zerocopy-release-package-"
        ) as target_directory:
            package_environment = dict(self._environment)
            package_environment["CARGO_TARGET_DIR"] = target_directory
            # Packaging does not need either release credential. Keeping them
            # out of this subprocess narrows exposure if Cargo invokes a
            # repository-provided helper in a future version.
            for name in tuple(package_environment):
                if "TOKEN" in name.upper():
                    package_environment.pop(name)
            arguments = [
                *self._plan.cargo_command,
                "package",
                "--locked",
                "--no-verify",
                "--manifest-path",
                str(package.manifest_path),
                "--package",
                package.name,
                "--registry",
                "crates-io",
            ]
            # A consumer can be packaged before its just-bumped dependency is
            # public. Package order is already the release's dependency order,
            # so use earlier source manifests as temporary crates.io patches.
            # This is deliberately derived rather than duplicated in the plan:
            # adding or reordering packages has one source of truth.
            arguments.extend(self._local_patch_arguments(prior_packages))
            result = self._command_runner(arguments, package_environment)
            if result.returncode != 0:
                diagnostic = _redact_diagnostic(
                    result.stderr or result.stdout, self._environment
                )
                raise ReleaseError(
                    f"could not reproduce {package.name} {package.version} "
                    f"with cargo package: {diagnostic}"
                )
            reproduced = (
                pathlib.Path(target_directory)
                / "package"
                / f"{package.name}-{package.version}.crate"
            )
            actual = _sha256_file(reproduced, "repackaged release archive")
            if actual != package.sha256:
                raise ReleaseError(
                    f"repackaging {package.name} {package.version} from "
                    f"{package.manifest_path} produced SHA-256 {actual}, but "
                    f"the prepared release archive has {package.sha256}; "
                    "refusing to publish non-reproducible contents"
                )

    def _reconcile_package(
        self,
        package: PackagePlan,
        prior_packages: Sequence[PackagePlan],
    ) -> None:
        existing = self._registry.get_version(package)
        if existing is not None:
            self._require_matching_version(package, existing)
            self._report(
                f"{package.name} {package.version} already matches crates.io."
            )
            return

        if not self._environment.get("CARGO_REGISTRY_TOKEN"):
            raise ReleaseError(
                f"{package.name} {package.version} is absent from crates.io, "
                "but CARGO_REGISTRY_TOKEN is not set in the environment"
            )

        arguments = [
            *self._plan.cargo_command,
            "publish",
            "--locked",
            "--no-verify",
            "--manifest-path",
            str(package.manifest_path),
            "--package",
            package.name,
            "--registry",
            "crates-io",
        ]
        # Keep just-published dependencies local while Cargo constructs the
        # upload. This avoids coupling correctness to sparse-index propagation;
        # crates.io's exact-version API and checksum remain the authority after
        # upload.
        arguments.extend(self._local_patch_arguments(prior_packages))
        result = self._command_runner(arguments, self._cargo_environment)
        if result.returncode == 0:
            self._wait_for_matching_version(package)
            self._report(
                f"Published and verified {package.name} {package.version}."
            )
            return

        # A failed client process does not prove that the server rejected the
        # upload. First look for the exact desired artifact. This handles a
        # runner losing the response after crates.io committed the package.
        immediate = self._registry.get_version(package)
        if immediate is not None:
            self._require_matching_version(package, immediate)
            self._report(
                f"{package.name} {package.version} appeared despite cargo's "
                "failure; accepted the matching crates.io state."
            )
            return

        if _looks_forbidden(result):
            raise ReleaseError(self._trusted_publisher_guidance(package, result))

        try:
            self._wait_for_matching_version(package)
        except RegistryTimeout as timeout:
            diagnostic = _redact_diagnostic(
                result.stderr or result.stdout, self._environment
            )
            raise ReleaseError(
                f"cargo publish failed for {package.name} {package.version}, "
                "and the matching version did not appear on crates.io.\n"
                f"Cargo diagnostic: {diagnostic}"
            ) from timeout
        self._report(
            f"{package.name} {package.version} appeared after cargo's failure; "
            "accepted the matching crates.io state."
        )

    @staticmethod
    def _local_patch_arguments(
        packages: Sequence[PackagePlan],
    ) -> list[str]:
        arguments: list[str] = []
        for package in packages:
            # A JSON string is also a valid TOML basic string and safely quotes
            # spaces, backslashes, and punctuation in an absolute path.
            path = json.dumps(str(package.manifest_path.parent))
            arguments.extend(
                (
                    "--config",
                    f"patch.crates-io.{package.name}.path={path}",
                )
            )
        return arguments

    def _wait_for_matching_version(self, package: PackagePlan) -> None:
        # Query immediately, then sleep before each bounded retry. The complete
        # delay schedule is visible and injected, so tests never need to wait.
        version = self._registry.get_version(package)
        if version is not None:
            self._require_matching_version(package, version)
            return
        for delay in self._poll_delays:
            self._sleep(delay)
            version = self._registry.get_version(package)
            if version is not None:
                self._require_matching_version(package, version)
                return
        elapsed = sum(self._poll_delays)
        raise RegistryTimeout(
            f"{package.name} {package.version} did not appear on crates.io "
            f"after {elapsed:g} seconds of bounded polling"
        )

    @staticmethod
    def _require_matching_version(
        package: PackagePlan, version: RegistryVersion
    ) -> None:
        if version.yanked:
            raise ReleaseError(
                f"crates.io has {package.name} {package.version}, but that "
                "version is yanked; refusing to treat it as this release"
            )
        if version.checksum != package.sha256:
            raise ReleaseError(
                f"crates.io has {package.name} {package.version} with "
                f"checksum {version.checksum}, but this release expects "
                f"{package.sha256}"
            )

    def _trusted_publisher_guidance(
        self, package: PackagePlan, result: CommandResult
    ) -> str:
        diagnostic = _redact_diagnostic(
            result.stderr or result.stdout, self._environment
        )
        return (
            f"crates.io rejected publication of {package.name} "
            f"{package.version} with HTTP 403. Configure or correct the "
            f"Trusted Publisher for crate `{package.name}` with exactly:\n"
            f"  Owner: {self._plan.owner}\n"
            f"  Repository: {self._plan.repository_name}\n"
            f"  Workflow: {self._plan.workflow}\n"
            f"  Environment: {self._plan.environment}\n"
            f"  Crate: {package.name}\n"
            "Then rerun the release. The reconciler will accept any earlier "
            "packages whose versions and checksums already match.\n"
            f"Cargo diagnostic: {diagnostic}"
        )

    def _reconcile_github_release(self) -> None:
        target = self._github.tag_target()
        if target is not None and target != self._plan.sha:
            raise ReleaseError(
                f"GitHub tag {self._plan.tag} peels to {target}, not the "
                f"requested release commit {self._plan.sha}; refusing to "
                "move or replace an existing tag"
            )

        release_exists = self._github.release_exists()
        if target is None and release_exists:
            raise ReleaseError(
                f"GitHub release {self._plan.tag} exists, but its git tag "
                "does not; refusing to guess how to repair inconsistent state"
            )
        if target is not None and release_exists:
            self._report(
                f"GitHub tag and release {self._plan.tag} already match."
            )
            return

        result = self._github.create_release(tag_exists=target is not None)

        # Verify state even if `gh` failed: like crates.io publication, a
        # response can be lost after GitHub committed the change.
        final_target = self._github.tag_target()
        final_release_exists = self._github.release_exists()
        if final_target == self._plan.sha and final_release_exists:
            if result.returncode == 0:
                self._report(f"Created GitHub release {self._plan.tag}.")
            else:
                self._report(
                    f"GitHub release {self._plan.tag} appeared despite gh's "
                    "failure; accepted the matching state."
                )
            return

        diagnostic = _redact_diagnostic(
            result.stderr or result.stdout, self._environment
        )
        if result.returncode != 0:
            raise ReleaseError(
                f"could not create GitHub release {self._plan.tag}: "
                f"{diagnostic}"
            )
        if final_target != self._plan.sha:
            raise ReleaseError(
                f"GitHub created tag {self._plan.tag} at "
                f"{final_target or '<missing>'}, not {self._plan.sha}"
            )
        raise ReleaseError(
            f"GitHub did not expose release {self._plan.tag} after gh "
            "reported successful creation"
        )


def _looks_forbidden(result: CommandResult) -> bool:
    diagnostic = f"{result.stdout}\n{result.stderr}".lower()
    return (
        re.search(r"\b403\b", diagnostic) is not None
        or "forbidden" in diagnostic
        or "not valid for crate" in diagnostic
        or "access token is not valid" in diagnostic
    )


def _sha256_file(path: pathlib.Path, description: str) -> str:
    digest = hashlib.sha256()
    try:
        with path.open("rb") as source:
            for chunk in iter(lambda: source.read(1024 * 1024), b""):
                digest.update(chunk)
    except OSError as error:
        raise ReleaseError(f"could not read {description} {path}: {error}") from error
    return digest.hexdigest()


def _redact_diagnostic(
    diagnostic: str, environment: Mapping[str, str]
) -> str:
    redacted = diagnostic.strip() or "<no diagnostic output>"
    for name, secret in environment.items():
        if "TOKEN" in name.upper() and secret:
            redacted = redacted.replace(secret, "<redacted>")
    return redacted


def main(arguments: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("plan", type=pathlib.Path, help="release plan JSON")
    parser.add_argument(
        "--root",
        type=pathlib.Path,
        default=pathlib.Path.cwd(),
        help="base for relative manifest and archive paths (default: cwd)",
    )
    parsed = parser.parse_args(arguments)
    try:
        plan = ReleasePlan.from_file(parsed.plan, root=parsed.root)
        ReleaseReconciler(plan).run()
    except ReleaseError as error:
        print(f"release reconciliation failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
