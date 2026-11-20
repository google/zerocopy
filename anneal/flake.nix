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
          leanSha256 = "47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4";
        };
        aarch64-linux = {
          rustSha256 = "sha256-gWFajI7TJyjslQLZm4VWBBsKA6nYe1lNQwrgUp2hwSA=";
          leanPlatform = "linux_aarch64";
          leanSha256 = "fdb974c2cdb4627e090d5d4007b913e09d13c4868720fb5594e22808b3de9e37";
        };
        x86_64-darwin = {
          rustSha256 = "sha256-dBLHRLo3omD7KRq0D8lzg6XiQfDKWOMD6YTrLQhEneo=";
          leanPlatform = "darwin";
          leanSha256 = "c2fee70250444e46c1106a27bddfef948d1e563eef431eaac05bb946b2f73d3a";
        };
        aarch64-darwin = {
          rustSha256 = "sha256-X7ndqbjsmnjL6KZzNCxkVFJPzAsAjUqerD/wc1rxK5E=";
          leanPlatform = "darwin_aarch64";
          leanSha256 = "65f22a4f047738ec742667b3247e836a86ebf06eabc12655c3dee00637e37866";
        };
      };

      forAllSystems = nixpkgs.lib.genAttrs (builtins.attrNames platforms);
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
              mkdir -p "$out"
              extract_component() {
                local name="$1"
                local url="https://static.rust-lang.org/dist/${rustDate}/''${name}-nightly-${rustTarget}.tar.gz"
                echo "Downloading and extracting $name from $url..."
                mkdir -p tmp_extract
                curl -sSL "$url" | tar -xz -C tmp_extract
                local top_dir
                top_dir="$(ls tmp_extract | head -n 1)"
                local comp_dir
                comp_dir="$(find "tmp_extract/$top_dir" -mindepth 1 -maxdepth 1 -type d | head -n 1)"
                cp -r "$comp_dir"/* "$out"/
                rm -rf tmp_extract
              }
              extract_component "cargo"
              extract_component "rustc"
              extract_component "rust-std"
              extract_component "rustc-dev"
              extract_component "llvm-tools"
              extract_component "miri"
              echo "Downloading and extracting rust-src..."
              mkdir -p tmp_extract
              curl -sSL "https://static.rust-lang.org/dist/${rustDate}/rust-src-nightly.tar.gz" | tar -xz -C tmp_extract
              top_dir="$(ls tmp_extract | head -n 1)"
              cp -r "tmp_extract/$top_dir/rust-src"/* "$out"/
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
              mkdir -p "$out" tmp_extract
              tar --zstd -xf "$src" -C tmp_extract
              top_dir="$(ls tmp_extract | head -n 1)"
              cp -r "tmp_extract/$top_dir"/* "$out"/
              rm -rf tmp_extract

              expected_lean_sha="$(jq -er --arg prefix "Lean (version ${leanVersion}, ${pkgs.stdenv.hostPlatform.config}" '.distributions | to_entries[] | select(.key | startswith($prefix)).value' "$lockFile")"
              actual_lean_sha="$(sha256sum "$out/bin/lean" | awk '{print $1}')"
              if [ "$actual_lean_sha" != "$expected_lean_sha" ]; then
                echo "ERROR: bin/lean SHA-256 mismatch ($actual_lean_sha != $expected_lean_sha)" >&2
                exit 1
              fi

              while IFS=$'\t' read -r mod_name ext expected_sha; do
                rel_path="lib/lean/$(echo "$mod_name" | tr '.' '/').$ext"
                actual_sha="$(sha256sum "$out/$rel_path" | awk '{print $1}')"
                if [ "$actual_sha" != "$expected_sha" ]; then
                  echo "ERROR: foundation artifact $rel_path SHA-256 mismatch ($actual_sha != $expected_sha)" >&2
                  exit 1
                fi
              done < <(jq -r '.modules | to_entries[] | .key as $m | .value.parts | to_entries[] | [$m, .key, .value] | @tsv' "$lockFile")
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
          };

          omnibus-archive = pkgs.stdenv.mkDerivation {
            pname = "anneal-toolchain-omnibus";
            version = "0.1.0";

            dontUnpack = true;
            dontPatchELF = true;
            dontStrip = true;
            dontPatchShebangs = true;

            nativeBuildInputs = with pkgs; [
              gnutar
              zstd
            ] ++ pkgs.lib.optionals pkgs.stdenv.isLinux [
              patchelf
            ];

            rustToolchain = self.packages.${system}.rust-toolchain;
            leanToolchain = self.packages.${system}.lean-toolchain;
            rustcCapture = self.packages.${system}.rustc-capture;
            leanFoundation = ./trusted/lean;

            buildPhase = ''
              set -euo pipefail
              mkdir -p \
                "$TMPDIR/dist_staging/bin" \
                "$TMPDIR/dist_staging/lean" \
                "$TMPDIR/dist_staging/rust" \
                "$TMPDIR/dist_staging/share/anneal/trusted"

              cp -r "$rustToolchain"/* "$TMPDIR/dist_staging/rust/"
              cp -r "$leanToolchain"/* "$TMPDIR/dist_staging/lean/"
              cp "$rustcCapture/bin/anneal-rustc-capture" "$TMPDIR/dist_staging/bin/"
              cp -r "$leanFoundation" "$TMPDIR/dist_staging/share/anneal/trusted/lean"

              chmod -R u+w "$TMPDIR/dist_staging"
              rm -rf "$TMPDIR/dist_staging/rust/share/doc"

              ${pkgs.lib.optionalString pkgs.stdenv.isLinux ''
                # Point the Nix-built `anneal-rustc-capture` binary at the
                # standard Linux dynamic linker used by upstream `rustc` and
                # relative `$ORIGIN` RPATHs. `rust/` and `lean/` are unpacked
                # directly from upstream release archives with `dontPatchELF`.
                patchelf \
                  --set-interpreter "$(patchelf --print-interpreter "$rustToolchain/bin/rustc")" \
                  --set-rpath '$ORIGIN/../rust/lib' \
                  "$TMPDIR/dist_staging/bin/anneal-rustc-capture"
              ''}

              for path in \
                bin/anneal-rustc-capture \
                lean/bin/lean \
                rust/bin/cargo \
                rust/bin/rustc \
                share/anneal/trusted/lean/foundation-lock.json \
                share/anneal/trusted/lean/lean-toolchain; do
                if [ ! -f "$TMPDIR/dist_staging/$path" ]; then
                  echo "ERROR: expected archive entry missing: $path" >&2
                  exit 1
                fi
              done

              cd "$TMPDIR/dist_staging"
              tar -cf - bin lean rust share | zstd -T0 -6 -o "$out"
            '';
          };

          default = self.packages.${system}.omnibus-archive;
        });

      devShells = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
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
          };
        });
    };
}
