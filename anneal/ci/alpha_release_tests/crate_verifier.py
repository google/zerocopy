# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`alpha_release.py` tests for the crate archive verifier."""

from __future__ import annotations

from .support import (
    DEV_VERSION,
    gzip,
    inspect_crate_archive,
    io,
    lzma,
    _make_crate_bytes,
    Path,
    SCRIPT,
    subprocess,
    sys,
    tarfile,
    tempfile,
    tracemalloc,
    verify_crate_file,
)


class CrateVerifierCases:
    """`AlphaReleaseTests` methods for the crate archive verifier."""

    def test_crate_verifier_is_cargo_normalization_invariant_and_tamper_evident(self) -> None:
        commit = "c" * 40
        digest = "3" * 64
        version = "0.2.0-alpha.7"
        baseline = _make_crate_bytes(version=version, commit=commit, sha256=digest)
        inspected = inspect_crate_archive(
            baseline,
            version=version,
            expected_commit=commit,
            expected_sha256=digest,
        )

        # Simulate a minor `cargo` upgrade adding synthesized `[package]` keys
        # and toggling `.cargo_vcs_info.json` `dirty`: `crate_source_sha256`
        # must remain identical.
        re_normalized = _make_crate_bytes(
            version=version,
            commit=commit,
            sha256=digest,
            dirty=False,
            extra_gen_package_lines=(
                'readme = "README.md"\n'
                'autolib = true\n'
                'autobins = true\n'
                'autoexamples = true\n'
                'autotests = false\n'
                'build = "build.rs"\n'
                'resolver = "2"\n'
            ),
        )
        re_inspected = inspect_crate_archive(
            re_normalized,
            version=version,
            expected_commit=commit,
            expected_sha256=digest,
        )
        self.assertEqual(
            inspected.crate_source_sha256, re_inspected.crate_source_sha256
        )

        # Any source, mode, or extra-file change alters `crate_source_sha256`.
        edited_src = _make_crate_bytes(
            version=version,
            commit=commit,
            sha256=digest,
            lib_rs=b"pub fn verifier() { /* changed */ }\n",
        )
        edited_info = inspect_crate_archive(edited_src, version=version)
        self.assertNotEqual(
            inspected.crate_source_sha256, edited_info.crate_source_sha256
        )
        mode_flipped = _make_crate_bytes(
            version=version, commit=commit, sha256=digest, lib_mode=0o755
        )
        self.assertNotEqual(
            inspected.crate_source_sha256,
            inspect_crate_archive(mode_flipped, version=version).crate_source_sha256,
        )

        with tempfile.TemporaryDirectory(prefix="anneal-verify-cli-") as tmp:
            crate_file = Path(tmp) / f"cargo-anneal-{version}.crate"
            crate_file.write_bytes(baseline)
            self.assertEqual(
                verify_crate_file(
                    crate_file,
                    version=version,
                    commit=commit,
                    sha256=digest,
                    expected_source_sha256=inspected.crate_source_sha256,
                ),
                inspected.crate_source_sha256,
            )
            with self.assertRaisesRegex(ValueError, "crate_source_sha256"):
                verify_crate_file(
                    crate_file,
                    version=version,
                    commit=commit,
                    sha256=digest,
                    expected_source_sha256="9" * 64,
                )
            with self.assertRaisesRegex(
                ValueError, "invalid nonzero 64-hex expected_source_sha256"
            ):
                verify_crate_file(
                    crate_file,
                    version=version,
                    commit=commit,
                    sha256=digest,
                    expected_source_sha256="",
                )
            # CLI subcommands work identically from an unrelated working dir,
            # while passing an empty `--expected-source-sha256 ""` fails closed.
            cli_out = subprocess.check_output(
                [
                    sys.executable,
                    "-B",
                    str(SCRIPT),
                    "verify-crate",
                    "--crate",
                    str(crate_file),
                    "--version",
                    version,
                    "--commit",
                    commit,
                    "--sha256",
                    digest,
                    "--expected-source-sha256",
                    inspected.crate_source_sha256,
                ],
                cwd=tmp,
                text=True,
            ).strip()
            self.assertEqual(cli_out, inspected.crate_source_sha256)
            empty_exp = subprocess.run(
                [
                    sys.executable,
                    "-B",
                    str(SCRIPT),
                    "verify-crate",
                    "--crate",
                    str(crate_file),
                    "--version",
                    version,
                    "--commit",
                    commit,
                    "--sha256",
                    digest,
                    "--expected-source-sha256",
                    "",
                ],
                cwd=tmp,
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(empty_exp.returncode, 0)

        with gzip.GzipFile(fileobj=io.BytesIO(baseline), mode="rb") as raw_gz:
            plain_tar = raw_gz.read()
        nested_xz_crate = gzip.compress(lzma.compress(plain_tar))

        prefix = f"cargo-anneal-{version}/"
        tampered_cases = [
            (
                "nested_tar_xz_inside_gzip",
                nested_xz_crate,
                "corrupt .crate archive",
            ),
            (
                "explicit_package_build_in_orig",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    extra_orig_package_lines='build = "custom.rs"\n',
                ),
                "must not set package.build explicitly",
            ),
            (
                "unexpected_synthesized_build",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    extra_gen_package_lines='readme = "README.md"\nbuild = "evil.rs"\n',
                ),
                "unexpected synthesized package.build",
            ),
            (
                "missing_build_rs",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    omit_member="build.rs",
                ),
                "missing required .crate member: build.rs",
            ),
            (
                "missing_packaged_bundle",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    omit_member="packaged/bundled_resources.rs",
                ),
                "missing required .crate member: packaged/bundled_resources.rs",
            ),
            (
                "missing_packaged_theory_bundle",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    omit_member="packaged/bundled_theory.json",
                ),
                "missing required .crate member: packaged/bundled_theory.json",
            ),
            (
                "legacy_checked_in_trusted_bundle",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    extra_members=(
                        (
                            f"{prefix}src/bundled_resources.rs",
                            b"// legacy\n",
                            0o644,
                            tarfile.REGTYPE,
                        ),
                    ),
                ),
                "forbidden legacy checked-in bundle",
            ),
            (
                "legacy_checked_in_theory_bundle",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    extra_members=(
                        (
                            f"{prefix}src/bundled_theory.json",
                            b"{}\n",
                            0o644,
                            tarfile.REGTYPE,
                        ),
                    ),
                ),
                "forbidden legacy checked-in bundle",
            ),
            (
                "implicit_extra_bin",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    extra_members=(
                        (f"{prefix}src/bin/extra.rs", b"fn main() {}\n", 0o644, tarfile.REGTYPE),
                    ),
                ),
                "forbidden implicit bin",
            ),
            (
                "embedded_cargo_config",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    extra_members=(
                        (
                            f"{prefix}.cargo/config.toml",
                            b"[build]\nrustc-wrapper = 'evil'\n",
                            0o644,
                            tarfile.REGTYPE,
                        ),
                    ),
                ),
                "forbidden hidden or config path",
            ),
            (
                "embedded_rust_toolchain",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    extra_members=(
                        (
                            f"{prefix}rust-toolchain.toml",
                            b"[toolchain]\nchannel = 'nightly'\n",
                            0o644,
                            tarfile.REGTYPE,
                        ),
                    ),
                ),
                "forbidden rust-toolchain file",
            ),
            (
                "symlink_entry",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    extra_members=((f"{prefix}evil", b"", 0o777, tarfile.SYMTYPE),),
                ),
                "non-regular tar entry",
            ),
            (
                "dir_entry",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    extra_members=((f"{prefix}src", b"", 0o755, tarfile.DIRTYPE),),
                ),
                "non-regular tar entry",
            ),
            (
                "duplicate_member",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    extra_members=((f"{prefix}README.md", b"dup", 0o644, tarfile.REGTYPE),),
                ),
                "duplicate .crate member",
            ),
            (
                "outside_prefix",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    extra_members=(("other-0.1.0/src/lib.rs", b"", 0o644, tarfile.REGTYPE),),
                ),
                "outside",
            ),
            (
                "dotdot_segment",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    extra_members=((f"{prefix}src/../evil.rs", b"", 0o644, tarfile.REGTYPE),),
                ),
                "unnormalized",
            ),
            (
                "exec_manifest",
                _make_crate_bytes(
                    version=version, commit=commit, sha256=digest, manifest_mode=0o755
                ),
                "unexpected executable mode",
            ),
            (
                "missing_orig",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    omit_member="Cargo.toml.orig",
                ),
                "missing required .crate member",
            ),
            (
                "wrong_vcs_path",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    path_in_vcs="zerocopy",
                ),
                "path_in_vcs",
            ),
            (
                "pax_newline_in_path",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    extra_members=(
                        (
                            f"{prefix}{'a' * 90}/bundle.rs\nsrc/evil.rs",
                            b"",
                            0o644,
                            tarfile.REGTYPE,
                        ),
                    ),
                ),
                "unnormalized or unsafe",
            ),
            (
                "dep_drift",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    gen_dep_spec='{ version = "2.0" }',
                ),
                "diverged from Cargo.toml.orig",
            ),
            (
                "bin_path_redirect",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    bin_path="src/lib.rs",
                ),
                "diverged from Cargo.toml.orig",
            ),
            (
                "lib_path_redirect",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    extra_top_toml='\n[lib]\nname = "cargo_anneal"\npath = "src/main.rs"\n',
                ),
                "diverged from Cargo.toml.orig",
            ),
            (
                "target_underscore_build_deps",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    extra_top_toml="\n[target.'cfg(unix)'.build_dependencies]\ncc = \"1.0\"\n",
                ),
                "unexpected keys",
            ),
            (
                "extra_lints_table_in_gen",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    extra_top_toml='\n[lints.rust]\nunsafe_code = "allow"\n',
                ),
                "diverged from Cargo.toml.orig",
            ),
            (
                "patch_table_injection",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    extra_top_toml='\n[patch.crates-io]\nserde = { path = "x" }\n',
                ),
                "unexpected top-level keys",
            ),
            (
                "unexpected_bin",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    bin_name="anneal-rustc-capture",
                ),
                "cargo-anneal bin",
            ),
            (
                "lock_version_mismatch",
                _make_crate_bytes(
                    version=version,
                    commit=commit,
                    sha256=digest,
                    lock_version=DEV_VERSION,
                ),
                "Cargo.lock cargo-anneal version mismatch",
            ),
        ]
        for label, payload, pattern in tampered_cases:
            with self.subTest(case=label), self.assertRaisesRegex(
                ValueError, pattern
            ):
                inspect_crate_archive(
                    payload,
                    version=version,
                    expected_commit=commit,
                    expected_sha256=digest,
                )

    def test_crate_verifier_bounds_memory_on_sparse_oversized_and_corrupt_streams(
        self,
    ) -> None:
        version = "0.2.0-alpha.7"
        prefix = f"cargo-anneal-{version}/"

        # 1. Corrupt deflate stream after valid gzip header raises ValueError.
        good = _make_crate_bytes(version=version, commit="c" * 40, sha256="3" * 64)
        corrupt_deflate = good[:10] + b"\x01\xff\xff\x00\x00\xde\xad\xbe\xef"
        with self.assertRaisesRegex(ValueError, "corrupt .crate archive"):
            inspect_crate_archive(corrupt_deflate, version=version)

        # 2. Crafted USTAR member declaring 512 MiB fails before
        # reading/allocating.
        huge = tarfile.TarInfo(f"{prefix}src/huge.bin")
        huge.type = tarfile.REGTYPE
        huge.size = 512 * 1024 * 1024
        oversized_tar = huge.tobuf(tarfile.USTAR_FORMAT) + b"\x00" * 1024
        oversized_crate = gzip.compress(oversized_tar, mtime=0)
        tracemalloc.start()
        try:
            with self.assertRaisesRegex(ValueError, "exceeds 64 MiB limit"):
                inspect_crate_archive(oversized_crate, version=version)
            _, peak_bytes = tracemalloc.get_traced_memory()
        finally:
            tracemalloc.stop()
        self.assertLess(peak_bytes, 4 * 1024 * 1024)

        # 3. PAX sparse entry (isreg() == True, issparse() == True) is rejected.
        def pax_record(key: str, value: str) -> bytes:
            body = f" {key}={value}\n".encode("utf-8")
            n = len(body) + 1
            while True:
                line = f"{n}".encode("ascii") + body
                if len(line) == n:
                    return line
                n = len(line)

        pax_data = (
            pax_record("GNU.sparse.major", "1")
            + pax_record("GNU.sparse.minor", "0")
            + pax_record("GNU.sparse.name", f"{prefix}src/sparse.bin")
            + pax_record("GNU.sparse.realsize", str(128 * 1024 * 1024))
        )
        pax_hdr = tarfile.TarInfo("PaxHeader/sparse.bin")
        pax_hdr.type = tarfile.XHDTYPE
        pax_hdr.size = len(pax_data)
        sparse_reg = tarfile.TarInfo(f"{prefix}src/sparse.bin")
        sparse_reg.type = tarfile.REGTYPE
        sparse_payload = b"1\n0\n0\n"
        sparse_reg.size = len(sparse_payload)
        pax_pad = b"\x00" * ((512 - len(pax_data) % 512) % 512)
        reg_pad = b"\x00" * ((512 - len(sparse_payload) % 512) % 512)
        sparse_tar = (
            pax_hdr.tobuf(tarfile.PAX_FORMAT)
            + pax_data
            + pax_pad
            + sparse_reg.tobuf(tarfile.PAX_FORMAT)
            + sparse_payload
            + reg_pad
            + b"\x00" * 1024
        )
        sparse_crate = gzip.compress(sparse_tar, mtime=0)
        tracemalloc.start()
        try:
            with self.assertRaisesRegex(ValueError, "non-regular tar entry"):
                inspect_crate_archive(sparse_crate, version=version)
            _, sparse_peak = tracemalloc.get_traced_memory()
        finally:
            tracemalloc.stop()
        self.assertLess(sparse_peak, 4 * 1024 * 1024)

        # 4. Cumulative payload size (> remaining) fails before allocation.
        first = tarfile.TarInfo(f"{prefix}src/first.bin")
        first.type = tarfile.REGTYPE
        first_payload = b"x" * 1024
        first.size = len(first_payload)
        second = tarfile.TarInfo(f"{prefix}src/second.bin")
        second.type = tarfile.REGTYPE
        second.size = 64 * 1024 * 1024
        cumulative_tar = (
            first.tobuf(tarfile.USTAR_FORMAT)
            + first_payload
            + second.tobuf(tarfile.USTAR_FORMAT)
            + b"\x00" * 1024
        )
        cumulative_crate = gzip.compress(cumulative_tar, mtime=0)
        tracemalloc.start()
        try:
            with self.assertRaisesRegex(ValueError, "exceeds 64 MiB limit"):
                inspect_crate_archive(cumulative_crate, version=version)
            _, cum_peak = tracemalloc.get_traced_memory()
        finally:
            tracemalloc.stop()
        self.assertLess(cum_peak, 4 * 1024 * 1024)

        # 5. Uncompressed stream > 64 MiB fails closed via chunked reader.
        gz_bomb = gzip.compress(b"\x00" * (64 * 1024 * 1024 + 1), mtime=0)
        with self.assertRaisesRegex(ValueError, "exceeds 64 MiB limit"):
            inspect_crate_archive(gz_bomb, version=version)
