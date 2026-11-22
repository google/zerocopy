# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

{
  description = "Anneal Hermetic Toolchain & Exocrate Archive Flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs, ... }:
    let
      rustDate = "2026-05-31";
      leanVersion =
        nixpkgs.lib.removePrefix "leanprover/lean4:v"
          (nixpkgs.lib.strings.trim (builtins.readFile ./trusted/lean/lean-toolchain));

      platforms = {
        x86_64-linux = {
          rustSha256 = "sha256-MmvOgC3shIOVMWT1MTRajw8JuLwRk/P3LsmGVslNGKw=";
          leanPlatform = "linux";
          leanLockTriple = "x86_64-unknown-linux-gnu";
          leanSha256 = "47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4";
        };
        aarch64-linux = {
          rustSha256 = "sha256-gWFajI7TJyjslQLZm4VWBBsKA6nYe1lNQwrgUp2hwSA=";
          leanPlatform = "linux_aarch64";
          leanLockTriple = "aarch64-unknown-linux-gnu";
          leanSha256 = "fdb974c2cdb4627e090d5d4007b913e09d13c4868720fb5594e22808b3de9e37";
        };
        x86_64-darwin = {
          rustSha256 = "sha256-dBLHRLo3omD7KRq0D8lzg6XiQfDKWOMD6YTrLQhEneo=";
          leanPlatform = "darwin";
          leanLockTriple = "x86_64-apple-darwin";
          leanSha256 = "c2fee70250444e46c1106a27bddfef948d1e563eef431eaac05bb946b2f73d3a";
        };
        aarch64-darwin = {
          rustSha256 = "sha256-X7ndqbjsmnjL6KZzNCxkVFJPzAsAjUqerD/wc1rxK5E=";
          leanPlatform = "darwin_aarch64";
          leanLockTriple = "arm64-apple-darwin";
          leanSha256 = "65f22a4f047738ec742667b3247e836a86ebf06eabc12655c3dee00637e37866";
        };
      };

      forAllSystems = nixpkgs.lib.genAttrs (builtins.attrNames platforms);

      rustBuildEnvironment = system:
        let
          pkgs = import nixpkgs { inherit system; };
          # rustc_private metadata and libLLVM must come from the same pinned
          # distribution as the compiler used to build the driver. Keep that
          # distribution unchanged: its Linux binaries use the host ELF loader,
          # so use Nix's loader and linker for builds and compiler queries.
          rustToolchain = self.packages.${system}.rust-toolchain;
          rustRuntimeLibraryPath = pkgs.lib.makeLibraryPath (
            [ rustToolchain ] ++ pkgs.lib.optionals pkgs.stdenv.isLinux [
              pkgs.stdenv.cc.cc.lib
              pkgs.stdenv.cc.libc
              pkgs.zlib
            ]
          );
          rustCompilerForBuild = if pkgs.stdenv.isLinux then
            pkgs.writeShellScript "anneal-build-rustc" ''
              # Copyright 2026 The Fuchsia Authors
              #
              # Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
              # <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
              # license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
              # This file may not be copied, modified, or distributed except according to
              # those terms.

              exec ${pkgs.stdenv.cc.bintools.dynamicLinker} \
                --library-path ${rustRuntimeLibraryPath} \
                ${rustToolchain}/bin/rustc --sysroot ${rustToolchain} \
                -Clinker-features=-lld "$@"
            ''
          else "${rustToolchain}/bin/rustc";

          # Compiler-session tests query bin/rustc in their sysroot. Keep the
          # pinned libraries unchanged, but route that query through the same
          # loader wrapper used to build the driver inside Nix's sandbox.
          testSysroot = if pkgs.stdenv.isLinux then pkgs.symlinkJoin {
            name = "anneal-test-sysroot";
            paths = [ rustToolchain ];
            postBuild = ''
              rm "$out/bin/rustc"
              ln -s "${rustCompilerForBuild}" "$out/bin/rustc"
            '';
          } else rustToolchain;
        in
        {
          inherit rustToolchain rustRuntimeLibraryPath rustCompilerForBuild testSysroot;
        };
    in
    {
      packages = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
          platform = platforms.${system};
          rustTarget = pkgs.stdenv.hostPlatform.rust.rustcTarget;

          leanArchive = pkgs.fetchurl {
            name = "lean-${leanVersion}-${platform.leanPlatform}.tar.zst";
            url = "https://github.com/leanprover/lean4/releases/download/v${leanVersion}/lean-${leanVersion}-${platform.leanPlatform}.tar.zst";
            sha256 = platform.leanSha256;
          };

          rustcCaptureSourceFiles = pkgs.lib.fileset.toSource {
            root = ./.;
            fileset = pkgs.lib.fileset.unions [
              ./Cargo.lock
              ./trusted/rustc-capture
            ];
          };

          rust = rustBuildEnvironment system;
          inherit (rust) rustToolchain rustRuntimeLibraryPath rustCompilerForBuild;
        in
        {
          # Download and unpack the multi-component Rust toolchain as a
          # fixed-output derivation without patching or stripping binaries.
          rust-toolchain = pkgs.stdenv.mkDerivation {
            pname = "rust-toolchain-${system}";
            version = rustDate;

            dontUnpack = true;
            dontPatchShebangs = true;
            dontPatchELF = true;
            dontStrip = true;

            outputHashMode = "recursive";
            outputHashAlgo = "sha256";
            outputHash = platform.rustSha256;

            nativeBuildInputs = with pkgs; [
              curl
              cacert
              gnutar
              gzip
            ];

            SSL_CERT_FILE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";

            buildPhase = ''
              set -euo pipefail
              mkdir -p "$out" tmp_extract
              # Download and decompress all 7 upstream component tarballs in
              # parallel into isolated slot directories, then merge them into
              # `$out` in deterministic order so the fixed-output NAR hash stays
              # bit-for-bit identical across all platforms.
              fetch_and_unpack() {
                (
                  set -euo pipefail
                  local slot="$1"
                  local label="$2"
                  local url="$3"
                  mkdir -p "tmp_extract/$slot"
                  echo "Downloading and extracting $label from $url..."
                  curl -fsSL "$url" | tar -xz -C "tmp_extract/$slot"
                )
              }
              components=(cargo rustc rust-std rustc-dev llvm-tools miri)
              pids=()
              for idx in "''${!components[@]}"; do
                comp="''${components[$idx]}"
                fetch_and_unpack "$idx" "$comp" \
                  "https://static.rust-lang.org/dist/${rustDate}/''${comp}-nightly-${rustTarget}.tar.gz" &
                pids+=("$!")
              done
              fetch_and_unpack 6 "rust-src" \
                "https://static.rust-lang.org/dist/${rustDate}/rust-src-nightly.tar.gz" &
              pids+=("$!")
              for pid in "''${pids[@]}"; do
                wait "$pid"
              done
              for idx in "''${!components[@]}"; do
                top_dir="$(ls "tmp_extract/$idx" | sed -n '1p')"
                test -n "$top_dir"
                comp_dir="$(find "tmp_extract/$idx/$top_dir" -mindepth 1 -maxdepth 1 -type d | sed -n '1p')"
                test -n "$comp_dir"
                test -d "$comp_dir"
                cp -r "$comp_dir"/* "$out"/
                rm -rf "tmp_extract/$idx"
              done
              top_dir="$(ls tmp_extract/6 | sed -n '1p')"
              test -n "$top_dir"
              test -d "tmp_extract/6/$top_dir/rust-src"
              cp -r "tmp_extract/6/$top_dir/rust-src"/* "$out"/
              rm -rf tmp_extract
            '';
          };

          # Unpack Lean without patchelf or strip and verify that `bin/lean` and
          # all `Init.*` artifacts match `trusted/lean/foundation-lock.json`.
          lean-toolchain = pkgs.stdenv.mkDerivation {
            pname = "lean-toolchain-${system}";
            version = leanVersion;
            src = leanArchive;
            lockFile = ./trusted/lean/foundation-lock.json;

            dontUnpack = true;
            dontPatchELF = true;
            dontStrip = true;
            dontPatchShebangs = true;

            nativeBuildInputs = with pkgs; [
              coreutils
              gnutar
              jq
              zstd
            ];

            buildPhase = ''
              set -euo pipefail
              mkdir -p "$out"
              tar --zstd --strip-components=1 -xf "$src" -C "$out"

              # Match Lean's reported distribution triple rather than Nix's
              # `hostPlatform.config` (`aarch64-apple-darwin` vs Lean's
              # `arm64-apple-darwin...`) and fail closed unless one entry
              # matches.
              expected_lean_sha="$(jq -er --arg prefix "Lean (version ${leanVersion}, ${platform.leanLockTriple}" '
                [
                  .distributions | to_entries[]
                  | select(
                      (.key | startswith($prefix))
                      and ((.key | ltrimstr($prefix)) | test("^([0-9]+(\\.[0-9]+)*)?, "))
                    )
                ] as $matches
                | if ($matches | length) == 1 then
                    $matches[0].value
                  else
                    error("expected unique distribution match for \($prefix), found \($matches | length)")
                  end
              ' "$lockFile")"
              actual_lean_sha="$(sha256sum "$out/bin/lean" | awk '{print $1}')"
              if [ "$actual_lean_sha" != "$expected_lean_sha" ]; then
                echo "ERROR: bin/lean SHA-256 mismatch ($actual_lean_sha != $expected_lean_sha)" >&2
                exit 1
              fi

              while IFS=$'\t' read -r mod_name ext expected_sha; do
                rel_path="lib/lean/$(echo "$mod_name" | tr '.' '/').$ext"
                if [ "$expected_sha" = "null" ]; then
                  if [ -e "$out/$rel_path" ] || [ -L "$out/$rel_path" ]; then
                    echo "ERROR: unexpected foundation companion $rel_path" >&2
                    exit 1
                  fi
                else
                  actual_sha="$(sha256sum "$out/$rel_path" | awk '{print $1}')"
                  if [ "$actual_sha" != "$expected_sha" ]; then
                    echo "ERROR: foundation artifact $rel_path SHA-256 mismatch ($actual_sha != $expected_sha)" >&2
                    exit 1
                  fi
                fi
              done < <(jq -r '.modules | to_entries[] | .key as $m | .value.parts | to_entries[] | [$m, .key, (.value // "null")] | @tsv' "$lockFile")
            '';
          };

          rustc-capture = pkgs.rustPlatform.buildRustPackage {
            pname = "anneal-rustc-capture";
            version = "0.1.0";
            src = rustcCaptureSourceFiles;
            sourceRoot = "source/trusted/rustc-capture";
            postUnpack = ''
              cp "$sourceRoot/../../Cargo.lock" "$sourceRoot/Cargo.lock"
              chmod +w "$sourceRoot/Cargo.lock"
            '';
            cargoLock.lockFile = ./Cargo.lock;
            RUSTC = rustCompilerForBuild;
            RUSTFLAGS = "-Lnative=${rustToolchain}/lib"
              + pkgs.lib.optionalString pkgs.stdenv.isLinux
                " -Clink-arg=-Wl,-rpath,${rustRuntimeLibraryPath}"
              + pkgs.lib.optionalString pkgs.stdenv.isDarwin
                " -Clink-arg=-Wl,-rpath,@executable_path/../rust/lib";
            LD_LIBRARY_PATH = rustRuntimeLibraryPath;
            DYLD_LIBRARY_PATH = "${rustToolchain}/lib";
            ANNEAL_TEST_RUST_SYSROOT = rust.testSysroot;

            # libLLVM loads zlib indirectly. Make it a direct dependency so
            # the driver's search path also resolves it on Linux, where an
            # executable's RUNPATH does not cover indirect dependencies.
            postFixup = pkgs.lib.optionalString pkgs.stdenv.isLinux ''
              ${pkgs.patchelf}/bin/patchelf --add-needed libz.so.1 \
                --set-rpath ${rustRuntimeLibraryPath} \
                "$out/bin/anneal-rustc-capture"
            '';
          };

          omnibus-archive = pkgs.stdenv.mkDerivation {
            pname = "anneal-toolchain-omnibus";
            version = "0.1.0";

            dontUnpack = true;
            dontPatchELF = true;
            dontStrip = true;
            dontPatchShebangs = true;

            nativeBuildInputs = with pkgs; [
              coreutils
              gnugrep
              gnused
              gnutar
              jq
              zstd
            ] ++ pkgs.lib.optionals pkgs.stdenv.isLinux [
              patchelf
            ];

            rustToolchain = self.packages.${system}.rust-toolchain;
            leanToolchain = self.packages.${system}.lean-toolchain;
            rustcCapture = self.packages.${system}.rustc-capture;
            leanFoundation = ./trusted/lean;
            leanTheory = ./theory;
            targetInspector = ./trusted/audit/TrustedBoundary.lean;
            targetLibraryLock = ./trusted/audit/library-lock.json;
            bundledResources = ./trusted/cargo-anneal/src/bundled_resources.rs;

            buildPhase = ''
              set -euo pipefail
              mkdir -p \
                "$TMPDIR/dist_staging/bin" \
                "$TMPDIR/dist_staging/share/anneal/trusted/audit"

              cp "$rustcCapture/bin/anneal-rustc-capture" "$TMPDIR/dist_staging/bin/"
              cp -r "$leanFoundation" "$TMPDIR/dist_staging/share/anneal/trusted/lean"
              cp -r "$leanTheory" "$TMPDIR/dist_staging/share/anneal/theory"
              cp "$targetInspector" "$TMPDIR/dist_staging/share/anneal/trusted/audit/TrustedBoundary.lean"
              cp "$targetLibraryLock" "$TMPDIR/dist_staging/share/anneal/trusted/audit/library-lock.json"

              # Copy correspondence provenance verbatim from the parity-checked
              # `CORRESPONDENCE_PROVENANCE_JSON` constant embedded in
              # `bundled_resources.rs` so the archive metadata and `cargo-anneal
              # verify` receipts share one canonical source of truth.
              provenance_literal="$(sed -n \
                's/^const CORRESPONDENCE_PROVENANCE_JSON: &str = \(.*\);$/\1/p' \
                "$bundledResources")"
              if [ "$(printf '%s\n' "$provenance_literal" | sed '/^$/d' | wc -l)" -ne 1 ]; then
                echo "ERROR: expected unique CORRESPONDENCE_PROVENANCE_JSON in $bundledResources" >&2
                exit 1
              fi
              printf '%s\n' "$provenance_literal" \
                | jq -e -r . \
                > "$TMPDIR/dist_staging/share/anneal/correspondence-provenance.json"
              jq -e 'type == "object" and .schema_version == 1' \
                "$TMPDIR/dist_staging/share/anneal/correspondence-provenance.json" \
                > /dev/null

              chmod -R u+w "$TMPDIR/dist_staging"

              ${pkgs.lib.optionalString pkgs.stdenv.isLinux ''
                # Carry the compiler's non-libc runtime dependencies beside
                # its libraries. Dereference the Nix symlinks so relocation
                # cannot silently depend on the build machine's store.
                mkdir -p "$TMPDIR/dist_staging/rust/lib"
                cp -L "${pkgs.zlib}/lib/libz.so.1" \
                  "$TMPDIR/dist_staging/rust/lib/libz.so.1"
                cp -L "${pkgs.stdenv.cc.cc.lib}/lib/libgcc_s.so.1" \
                  "$TMPDIR/dist_staging/rust/lib/libgcc_s.so.1"
                chmod u+w \
                  "$TMPDIR/dist_staging/rust/lib/libz.so.1" \
                  "$TMPDIR/dist_staging/rust/lib/libgcc_s.so.1"

                # Point the Nix-built `anneal-rustc-capture` binary at the
                # standard Linux dynamic linker used by upstream `rustc` and
                # relative `$ORIGIN` RPATHs. `rust/` and `lean/` are unpacked
                # directly from upstream release archives with `dontPatchELF`.
                patchelf \
                  --set-interpreter "$(patchelf --print-interpreter "$rustToolchain/bin/rustc")" \
                  --set-rpath '$ORIGIN/../rust/lib' \
                  "$TMPDIR/dist_staging/bin/anneal-rustc-capture"
              ''}

              for full_path in \
                "$TMPDIR/dist_staging/bin/anneal-rustc-capture" \
                "$leanToolchain/bin/lean" \
                "$rustToolchain/bin/cargo" \
                "$rustToolchain/bin/rustc" \
                "$TMPDIR/dist_staging/share/anneal/correspondence-provenance.json" \
                "$TMPDIR/dist_staging/share/anneal/trusted/audit/TrustedBoundary.lean" \
                "$TMPDIR/dist_staging/share/anneal/trusted/audit/library-lock.json" \
                "$TMPDIR/dist_staging/share/anneal/trusted/lean/foundation-lock.json" \
                "$TMPDIR/dist_staging/share/anneal/trusted/lean/lean-toolchain" \
                "$TMPDIR/dist_staging/share/anneal/trusted/lean/Trusted/MirAst.lean" \
                "$TMPDIR/dist_staging/share/anneal/trusted/lean/Trusted/MirSemantics.lean" \
                "$TMPDIR/dist_staging/share/anneal/theory/Anneal.lean" \
                "$TMPDIR/dist_staging/share/anneal/theory/Anneal/MirWp.lean"; do
                if [ ! -f "$full_path" ]; then
                  echo "ERROR: expected archive entry missing: $full_path" >&2
                  exit 1
                fi
              done

              # Stream `lean/` and `rust/` directly from their verified store
              # paths without copying 3.3 GiB into `$TMPDIR`. `flags=r`
              # rewrites member paths without altering internal `.so` symlink
              # targets, `--hard-dereference` breaks store hardlinks into
              # standalone files, and `--mode='u+w'` makes entries writable.
              lean_parent="$(dirname "$leanToolchain")"
              lean_base="$(basename "$leanToolchain")"
              lean_esc="$(printf '%s' "$lean_base" | sed 's/[.[\*^$:]/\\&/g')"
              rust_parent="$(dirname "$rustToolchain")"
              rust_base="$(basename "$rustToolchain")"
              rust_esc="$(printf '%s' "$rust_base" | sed 's/[.[\*^$:]/\\&/g')"

              tar_args=(
                --mode='u+w'
                --hard-dereference
                --anchored
                --exclude="$rust_base/share/doc"
              )
              ${pkgs.lib.optionalString pkgs.stdenv.isLinux ''
                tar_args+=(
                  --exclude="$rust_base/lib/libz.so.1"
                  --exclude="$rust_base/lib/libgcc_s.so.1"
                )
              ''}
              tar_args+=(
                --transform="flags=r;s:^''${lean_esc}\$:lean:;s:^''${lean_esc}/:lean/:"
                --transform="flags=r;s:^''${rust_esc}\$:rust:;s:^''${rust_esc}/:rust/:"
                -cf -
                -C "$TMPDIR/dist_staging" bin share
                -C "$lean_parent" "$lean_base"
                -C "$rust_parent" "$rust_base"
              )
              ${pkgs.lib.optionalString pkgs.stdenv.isLinux ''
                tar_args+=(
                  -C "$TMPDIR/dist_staging"
                  rust/lib/libz.so.1
                  rust/lib/libgcc_s.so.1
                )
              ''}

              tar "''${tar_args[@]}" | zstd -T"$NIX_BUILD_CORES" -3 -o "$out"

              # Verify the produced archive directly so any broken path
              # transform or unexpected top-level member fails closed at build
              # time before downstream jobs or release uploads consume `$out`.
              zstd -dc "$out" | tar -tf - > "$TMPDIR/archive_entries.txt"
              if grep -Eqv '^(bin|lean|rust|share)(/|$)' "$TMPDIR/archive_entries.txt"; then
                echo "ERROR: unexpected top-level entry in omnibus archive" >&2
                exit 1
              fi
              if grep -Eq '^rust/share/doc(/|$)' "$TMPDIR/archive_entries.txt"; then
                echo "ERROR: rust/share/doc was not excluded from omnibus archive" >&2
                exit 1
              fi
              expected_entries=(
                bin/anneal-rustc-capture
                lean/bin/lean
                rust/bin/cargo
                rust/bin/rustc
                share/anneal/correspondence-provenance.json
                share/anneal/trusted/audit/TrustedBoundary.lean
                share/anneal/trusted/audit/library-lock.json
                share/anneal/trusted/lean/foundation-lock.json
                share/anneal/trusted/lean/lean-toolchain
                share/anneal/trusted/lean/Trusted/MirAst.lean
                share/anneal/trusted/lean/Trusted/MirSemantics.lean
                share/anneal/theory/Anneal.lean
                share/anneal/theory/Anneal/MirWp.lean
              )
              ${pkgs.lib.optionalString pkgs.stdenv.isLinux ''
                expected_entries+=(
                  rust/lib/libz.so.1
                  rust/lib/libgcc_s.so.1
                )
              ''}
              for entry in "''${expected_entries[@]}"; do
                if ! grep -Fxq -- "$entry" "$TMPDIR/archive_entries.txt"; then
                  echo "ERROR: expected archive entry missing from $out: $entry" >&2
                  exit 1
                fi
              done
            '';
          };

          # Release regressions need Python, the pinned YAML parser, and jq.
          release-check-python = pkgs.symlinkJoin {
            name = "anneal-release-check-python";
            paths = [
              (pkgs.python3.withPackages (p: [ p.pyyaml ]))
              pkgs.jq
            ];
          };

          default = self.packages.${system}.omnibus-archive;
        });

      devShells = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
          rust = rustBuildEnvironment system;
        in
        {
          default = pkgs.mkShell {
            packages = [
              self.packages.${system}.lean-toolchain
              self.packages.${system}.rust-toolchain
              self.packages.${system}.rustc-capture
              pkgs.zstd
              pkgs.jq
            ];
            ANNEAL_TEST_RUST_SYSROOT = rust.testSysroot;
          };
        });
    };
}
