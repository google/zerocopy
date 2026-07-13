{
  description = "Clean Aeneas Downloader Derivation";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = true;
        };

        # Upstream platform names.
        rustPlatform = if system == "x86_64-linux" then "x86_64-unknown-linux-gnu"
                       else if system == "aarch64-linux" then "aarch64-unknown-linux-gnu"
                       else if system == "x86_64-darwin" then "x86_64-apple-darwin"
                       else if system == "aarch64-darwin" then "aarch64-apple-darwin"
                       else throw "Unsupported system: ${system}";

        leanPlatform = if system == "x86_64-linux" then "linux"
                       else if system == "aarch64-linux" then "linux_aarch64"
                       else if system == "x86_64-darwin" then "darwin"
                       else if system == "aarch64-darwin" then "darwin_aarch64"
                       else throw "Unsupported system: ${system}";

        aeneasTarget = if system == "x86_64-linux" then "linux-x86_64"
                       else if system == "aarch64-linux" then "linux-aarch64"
                       else if system == "x86_64-darwin" then "macos-x86_64"
                       else if system == "aarch64-darwin" then "macos-aarch64"
                       else throw "Unsupported system: ${system}";

        aeneasSha256 = if system == "x86_64-linux" then "sha256-APuO9CfU0G3KvZD1GWJm4HcxrfKnRmlkzm9PbR6MvBE="
                       else if system == "aarch64-linux" then "sha256-JUAsTLy32i0zfLFoZjVCvJx1rpsQ0tJwj1KJ6MqdGQI="
                       else if system == "x86_64-darwin" then "sha256-uiXuhXp2+o9MECL23/QHLJoBAHRT1nxhz7qhqhwD4xc="
                       else if system == "aarch64-darwin" then "sha256-dveLZF4zjsfokynwrSJ5KZf0K9m16xRkOsMq3iJO62E="
                       else throw "Unsupported system: ${system}";

        rustDate = "2026-05-31";
        leanVersion = "v4.30.0-rc2";

        rustToolchainSha256 = if system == "x86_64-linux" then "sha256-MmvOgC3shIOVMWT1MTRajw8JuLwRk/P3LsmGVslNGKw="
                              else if system == "aarch64-linux" then "sha256-gWFajI7TJyjslQLZm4VWBBsKA6nYe1lNQwrgUp2hwSA="
                              else if system == "x86_64-darwin" then "sha256-dBLHRLo3omD7KRq0D8lzg6XiQfDKWOMD6YTrLQhEneo="
                              else if system == "aarch64-darwin" then "sha256-X7ndqbjsmnjL6KZzNCxkVFJPzAsAjUqerD/wc1rxK5E="
                              else throw "Unsupported system: ${system}";

        leanToolchainSha256 = if system == "x86_64-linux" then "sha256-o47cQjSLK5YL8YZ2raaj+mGAvvO+dIDfVeP2L+WoyMs="
                              else if system == "aarch64-linux" then "sha256-IrEGcTEeI1q0/7tLtMiiKPcW05JvaU8kNY6y5eprYg4="
                              else if system == "x86_64-darwin" then "sha256-DDPmVkXjSLDr21LXcdvNkmGjD2v+sbUyY+REr3uylwI="
                              else if system == "aarch64-darwin" then "sha256-dpUCCLkhoGDKkDKPZxr7WrmkifxHi4MWLpD148z2vhg="
                              else throw "Unsupported system: ${system}";

        leantarPlatform = if system == "x86_64-linux" then "x86_64-unknown-linux-musl"
                          else if system == "aarch64-linux" then "aarch64-unknown-linux-musl"
                          else if system == "x86_64-darwin" then "x86_64-apple-darwin"
                          else if system == "aarch64-darwin" then "aarch64-apple-darwin"
                          else throw "Unsupported system: ${system}";

        leantarSha256 = if system == "x86_64-linux" then "sha256-LLxAyiFCJ6DlNnIcAhutcZqALdhrHy2JiVce+vv709E="
                        else if system == "aarch64-linux" then "sha256-Jut3VDaIPj1c2tJ681ucNyEscxBjFoY+ofxfjsLMneQ="
                        else if system == "x86_64-darwin" then "sha256-58eNYGxlMHhiuw/sWqRG1ves4TN7HkiVzEfZH3VlmWw="
                        else if system == "aarch64-darwin" then "sha256-tbWQ0vhC4jWZPsdW09vWCKE8iP1U02p7K2WjY7LuXjU="
                        else throw "Unsupported system: ${system}";

        mathlibCacheDownloadSha256 = if system == "x86_64-linux" then "sha256-n67tKjzZm5LsDU1Dl9kaOFKrQw+8YE201F0toYu1C3s="
                                     else if system == "aarch64-linux" then "sha256-9Yj5BAv6V5BTLd/nOWzIuqTDJPKwqR28bg7m9+46K98="
                                     else if system == "x86_64-darwin" then "sha256-DBdUmPfheeLTVwaVUzkB541Y9CWSQN6gmxBnJ3oxL4c="
                                     else if system == "aarch64-darwin" then "sha256-wv2NZcKiyYaW6L/o7+oHWZdYZhVYLzZjyQczoaHRJnk="
                                     else throw "Unsupported system: ${system}";

        linuxDynamicLinker = if system == "x86_64-linux" then "/lib64/ld-linux-x86-64.so.2"
                             else if system == "aarch64-linux" then "/lib/ld-linux-aarch64.so.1"
                             else "";

        linuxFhsEnv = if pkgs.stdenv.isLinux then pkgs.buildFHSEnv {
          name = "anneal-linux-fhs";
          targetPkgs = pkgs: with pkgs; [
            stdenv.cc.cc
            zlib
            gmp
            libffi
            ncurses
            openssl
          ];
          runScript = "bash";
        } else null;

        runLeanCommand = command:
          if pkgs.stdenv.isLinux
          then "${linuxFhsEnv}/bin/anneal-linux-fhs -c ${pkgs.lib.escapeShellArg command}"
          else command;

        # Prebuilt Aeneas release archive.
        fetchAeneas = { target, releaseTag, sha256 }:
          pkgs.fetchurl {
            name = "aeneas-${target}.tar.gz";
            url = "https://github.com/AeneasVerif/aeneas/releases/download/${releaseTag}/aeneas-${target}.tar.gz";
            inherit sha256;
          };

        # Fixed-output downloader used for toolchain assets.
        fetchToolchainAsset = { pname, version, sha256, buildPhase }:
          pkgs.stdenv.mkDerivation {
            pname = "${pname}-${system}";
            inherit version sha256 buildPhase;

            dontUnpack = true;

            # Keep downloaded toolchains byte-for-byte independent of the builder.
            dontPatchShebangs = true;
            dontPatchELF = true;
            dontStrip = true;

            outputHashMode = "recursive";
            outputHashAlgo = "sha256";
            outputHash = sha256;

            nativeBuildInputs = with pkgs; [
              curl
              cacert
              gnutar
              gzip
              zstd
            ];

            SSL_CERT_FILE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";
          };

        # Merge the Rust components into one sysroot.
        fetchRustToolchain = { rustDate, sha256 }:
          fetchToolchainAsset {
            pname = "rust-toolchain";
            version = rustDate;
            inherit sha256;

            buildPhase = builtins.concatStringsSep "\n" [
              "mkdir -p $out"
              # Rust archives nest each component under a top-level directory.
              "extract_component() {"
              "  local name=$1"
              "  local url=\"https://static.rust-lang.org/dist/${rustDate}/\${name}-nightly-${rustPlatform}.tar.gz\""
              "  echo \"Downloading and extracting $name from $url...\""
              "  mkdir -p tmp_extract"
              "  curl -sSL \"$url\" | tar -xz -C tmp_extract"
              "  local top_dir=$(ls tmp_extract | head -n 1)"
              "  local comp_dir=$(find \"tmp_extract/$top_dir\" -mindepth 1 -maxdepth 1 -type d | head -n 1)"
              "  cp -r $comp_dir/* $out/"
              "  rm -rf tmp_extract"
              "}"
              "extract_component \"cargo\""
              "extract_component \"rustc\""
              "extract_component \"rust-std\""
              "extract_component \"rustc-dev\""
              "extract_component \"llvm-tools\""
              "extract_component \"miri\""
              "echo \"Downloading and extracting rust-src...\""
              "mkdir -p tmp_extract"
              "curl -sSL \"https://static.rust-lang.org/dist/${rustDate}/rust-src-nightly.tar.gz\" | tar -xz -C tmp_extract"
              "local top_dir=$(ls tmp_extract | head -n 1)"
              "cp -r tmp_extract/$top_dir/rust-src/* $out/"
              "rm -rf tmp_extract"
            ];
          };

        # Download and unpack the Lean compiler toolchain.
        fetchLeanToolchain = { leanVersion, sha256 }:
          let
            # Lean archives omit the leading "v" in their filenames.
            rawVersion = if builtins.substring 0 1 leanVersion == "v"
                         then builtins.substring 1 (builtins.stringLength leanVersion - 1) leanVersion
                         else leanVersion;
          in
          fetchToolchainAsset {
            pname = "lean-toolchain";
            version = rawVersion;
            inherit sha256;

            buildPhase = builtins.concatStringsSep "\n" [
              "mkdir -p $out"
              "url=\"https://releases.lean-lang.org/lean4/${leanVersion}/lean-${rawVersion}-${leanPlatform}.tar.zst\""
              "echo \"Downloading Lean toolchain from $url...\""
              "curl -sSL \"$url\" | zstd -d | tar -x -C $out --strip-components=1"
            ];
          };

        fetchLeantar = { version, sha256 }:
          let
            archive = pkgs.fetchurl {
              name = "leantar-${version}-${leantarPlatform}.tar.gz";
              url = "https://github.com/digama0/leangz/releases/download/v${version}/leantar-v${version}-${leantarPlatform}.tar.gz";
              inherit sha256;
            };
          in
          pkgs.stdenv.mkDerivation {
            pname = "leantar-${system}";
            inherit version;

            src = archive;
            dontPatchShebangs = true;
            dontPatchELF = true;
            dontStrip = true;

            nativeBuildInputs = with pkgs; [
              gnutar
              gzip
            ];

            unpackPhase = ''
              runHook preUnpack
              tar -xzf "$src" --strip-components=1
              runHook postUnpack
            '';

            installPhase = ''
              runHook preInstall
              mkdir -p "$out/bin"
              cp leantar "$out/bin/leantar"
              chmod +x "$out/bin/leantar"
              runHook postInstall
            '';
          };

        buildAeneas = { mode, prepared, seed ? null }:
          let
            fast = mode == "fast";
            # Build exactly the same package-library inventory in both modes.
            # The fast build replays candidate artifacts; the slow build
            # produces the corresponding artifacts from Lean sources.
            fullPackageTargets = "@Cli/Cli @batteries/Batteries @Qq/Qq @aesop/Aesop @proofwidgets/ProofWidgets @importGraph/ImportGraph @LeanSearchClient/LeanSearchClient @plausible/Plausible @mathlib/Mathlib";
          in
          pkgs.stdenv.mkDerivation ({
            pname = "aeneas-compiled-${mode}";
            version = "0.1.0";

            # Lake records content hashes for its native artifacts. Preserve
            # those bytes after validation; the omnibus derivation only
            # normalizes executables outside `.lake`.
            dontPatchShebangs = true;
            dontPatchELF = true;
            dontStrip = true;

            src = pkgs.runCommand "empty-src" {} "mkdir $out";

            inherit prepared;
            leanToolchain = self.packages.${system}.lean-toolchain;

            nativeBuildInputs = with pkgs; [
              python3
              gnutar
              zstd
            ];

            buildPhase = builtins.concatStringsSep "\n" (
              [
                "export HOME=$TMPDIR/home"
                "export XDG_CACHE_HOME=$TMPDIR/cache"
                "mkdir -p \"$HOME\" \"$XDG_CACHE_HOME\""
                "unset CI"
                "export PATH=\"$leanToolchain/bin:\$PATH\""
                "export LEAN_SYSROOT=\"$leanToolchain\""
                # Let sandboxed Lean executables find libleanshared.so.
                "export LD_LIBRARY_PATH=\"$leanToolchain/lib:$leanToolchain/lib/lean:\$LD_LIBRARY_PATH\""
                # Every dependency is already vendored, and both builders must
                # stay offline after the shared preparation cut point.
                "export MATHLIB_NO_CACHE_ON_UPDATE=1"
                "mkdir -p aeneas"
                "cp -r $prepared/. aeneas/"
                "chmod -R +w aeneas"
              ]
              ++ pkgs.lib.optionals fast [
                "cp -r $seed/. aeneas/"
                "chmod -R +w aeneas"
                "test -f aeneas/packages/batteries/.lake/build/lib/lean/Batteries/Data/Array/Merge.olean"
              ]
              ++ pkgs.lib.optionals (!fast) [
                "if find aeneas -type d -name .lake -print -quit | grep -q .; then"
                "  echo \"ERROR: the slow build received prebuilt .lake state\" >&2"
                "  exit 1"
                "fi"
                "if find aeneas -type f \\( -name '*.hash' -o -name '*.olean' -o -name '*.ilean' \\) -print -quit | grep -q .; then"
                "  echo \"ERROR: the slow build received prebuilt Lean artifacts\" >&2"
                "  exit 1"
                "fi"
              ]
              ++ [
                # Copying can assign fresh directory mtimes. Source/config
                # files are normalized in both modes so only the fast cache
                # artifacts are newer when old mode checks them.
                "find aeneas -type f \\( -name '*.lean' -o -name 'lakefile.lean' -o -name 'lakefile.toml' -o -name 'lake-manifest.json' -o -name 'lean-toolchain' \\) -exec touch -h -d '1970-01-01 00:00:00' {} +"
                "cd aeneas/backends/lean"
              ]
              ++ pkgs.lib.optionals fast [
                # Materialize the same complete library target inventory as the
                # clean oracle. Existing candidate artifacts are accepted by
                # mtime, so only absent cache entries require compilation.
                (runLeanCommand "lake --no-cache --old build ${fullPackageTargets}")
                (runLeanCommand "lake --no-cache --old build")
                "test -f ../../packages/batteries/.lake/build/lib/lean/Batteries/Data/Array/Merge.olean"
              ]
              ++ pkgs.lib.optionals (!fast) [
                # There is no `.lake` state at this point. Build every vendored
                # Lean library before the root package so the oracle covers the
                # same candidate-artifact inventory without using its bytes.
                (runLeanCommand "lake --no-cache --rehash -R build ${fullPackageTargets}")
                (runLeanCommand "lake --no-cache --rehash -R build")
              ]
              ++ [
                # FIXME: Remove this v1-only workspace primer once generated
                # workspaces migrate to v2.
                "mkdir -p $TMPDIR/aeneas-config-primer/generated"
                "cp lean-toolchain $TMPDIR/aeneas-config-primer/lean-toolchain"
                "cat > $TMPDIR/aeneas-config-primer/generated/Generated.lean <<'EOF'"
                "import Aeneas"
                "EOF"
                "cp ${./prime-lakefile.lean} $TMPDIR/aeneas-config-primer/lakefile.lean"
                "chmod +w $TMPDIR/aeneas-config-primer/lakefile.lean"
                "substituteInPlace $TMPDIR/aeneas-config-primer/lakefile.lean --replace-fail @AENEAS_ROOT@ \"$PWD\""
              ]
              ++ pkgs.lib.optionals fast [
                # This is the fast path's sole trace refresh traversal.
                "(cd $TMPDIR/aeneas-config-primer && ${runLeanCommand "lake --no-cache run Anneal.refreshLakeTraces generated/Generated.lean"})"
              ]
              ++ pkgs.lib.optionals (!fast) [
                # Build the clean result in the same dependency context used by
                # InfoView, without invoking the fast trace promotion script.
                "(cd $TMPDIR/aeneas-config-primer && ${runLeanCommand "lake --no-cache --rehash -R setup-file generated/Generated.lean --quiet >/dev/null"})"
              ]
              ++ [
                "test -f .lake/config/aeneas/lakefile.olean"
                "python3 ${./rewrite-lake-vendor.py} --root . --packages-dir ../../packages --rewrite-traces --trace-prefix \"$leanToolchain=lean\""
                "TRACE_ABS_RE='(^|[\"[:space:]=:])/[A-Za-z0-9._~-]'"
                "if find . ../../packages -type f -name '*.trace' -exec grep -EIl \"\$TRACE_ABS_RE\" {} + | tee /tmp/non-relocatable-traces | grep -q .; then"
                "  echo \"ERROR: non-relocatable paths remain in Lake trace files\" >&2"
                "  cat /tmp/non-relocatable-traces >&2"
                "  exit 1"
                "fi"
                # Apply exactly the same closure pruning to the two builds.
                "python3 ${./prune-lake-cache.py} --project-root . --packages-root ../../packages"
                # This is a read-only assertion, not a repair round: ordinary
                # hash-mode InfoView setup must accept the finished package tree.
                "chmod -R a-w . ../../packages"
                "(cd $TMPDIR/aeneas-config-primer && ${runLeanCommand "lake --no-cache setup-file generated/Generated.lean --no-build --quiet >/dev/null"})"
                "if find . ../../packages -type f \\( -name '*.trace.nobuild' -o -name '*.anneal-tmp' \\) -print -quit | grep -q .; then"
                "  echo \"ERROR: Lake setup-file left repair metadata behind\" >&2"
                "  exit 1"
                "fi"
                "cd ../.."
                "mkdir -p $out/backends $out/packages $out/bin"
                "cp -r backends/lean $out/backends/"
                "cp -r packages/* $out/packages/"
                "cp -r bin/* $out/bin/"
              ]
            );
          }
          // pkgs.lib.optionalAttrs fast {
            inherit seed;
          }
          // pkgs.lib.optionalAttrs pkgs.stdenv.isDarwin {
            # nixpkgs' Darwin fixup hook otherwise rewrites every cached
            # `.dylib`/`.so` after Lake records its content hash.
            preFixup = ''
              fixDarwinDylibNamesIn() { :; }
            '';
          });
      in
      {
        packages.aeneas-download = fetchAeneas {
          target = aeneasTarget;
          releaseTag = "nightly-2026.06.03";
          sha256 = aeneasSha256;
        };

        # Extracts the toolchain metadata implied by the Aeneas archive.
        packages.aeneas-unpacked = pkgs.stdenv.mkDerivation {
          pname = "aeneas-unpacked";
          version = "1.0.0";

          src = self.packages.${system}.aeneas-download;

          nativeBuildInputs = with pkgs; [
            gnutar
            gzip
          ];

          dontUnpack = true;

          buildPhase = builtins.concatStringsSep "\n" [
            "mkdir -p $out"
            "tar -xzf $src -C $out"
            "chmod -R +w $out"
            "LEAN_RAW=\$(cat $out/backends/lean/lean-toolchain)"
            "LEAN_VERSION=\$(echo \"\$LEAN_RAW\" | sed -E 's|leanprover/lean4:v?||' | tr -d '\\n')"
            "if [ -z \"\$LEAN_VERSION\" ] || [ \"\$LEAN_VERSION\" = \"\$LEAN_RAW\" ]; then"
            "  echo \"ERROR: could not parse Lean toolchain from Aeneas archive: \$LEAN_RAW\" >&2"
            "  exit 1"
            "fi"
            "RUST_DATE=${rustDate}"
            "RUST_VERSION=\"nightly-\$RUST_DATE\""
            "cat <<EOF > $out/metadata.json"
            "{"
            "  \"lean-toolchain\": \"\$LEAN_VERSION\","
            "  \"rust-toolchain-date\": \"\$RUST_DATE\","
            "  \"rust-toolchain-version\": \"\$RUST_VERSION\""
            "}"
            "EOF"
          ];
        };

        # Minimal project metadata used to fetch the Mathlib cache.
        packages.aeneas-metadata-files = pkgs.stdenv.mkDerivation {
          pname = "aeneas-metadata-files";
          version = "1.0.0";

          src = self.packages.${system}.aeneas-download;

          nativeBuildInputs = with pkgs; [
            gnutar
            gzip
          ];

          dontUnpack = true;

          buildPhase = builtins.concatStringsSep "\n" [
            "mkdir -p $out"
            "tar -xzf $src -C $out --strip-components=2 \\"
            "  backends/lean/lakefile.lean \\"
            "  backends/lean/lake-manifest.json \\"
            "  backends/lean/lean-toolchain"
          ];
        };

        # Fetches Mathlib's precompiled Lake cache in a fixed-output derivation.
        packages.mathlib-cache-download = pkgs.stdenv.mkDerivation {
          pname = "mathlib-cache-download-${system}";
          version = "0.1.0";

          dontUnpack = true;

          # Preserve downloaded artifacts exactly.
          dontPatchShebangs = true;
          dontPatchELF = true;
          dontStrip = true;

          # This fixed-output fetch must preserve cached native artifacts
          # exactly; Darwin's generic fixup hook would rewrite them.
          preFixup = pkgs.lib.optionalString pkgs.stdenv.isDarwin ''
            fixDarwinDylibNamesIn() { :; }
          '';

          outputHashMode = "recursive";
          outputHashAlgo = "sha256";
          outputHash = mathlibCacheDownloadSha256;

          leanToolchainRaw = self.packages.${system}.lean-toolchain;
          metadataFiles = self.packages.${system}.aeneas-metadata-files;

          nativeBuildInputs = with pkgs; [
            git
            gnutar
            zstd
            curl
            cacert
          ];

          SSL_CERT_FILE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";

          buildPhase = builtins.concatStringsSep "\n" [
            "export HOME=$TMPDIR"
            "mkdir -p project"
            "cp $metadataFiles/lakefile.lean project/"
            "cp $metadataFiles/lake-manifest.json project/"
            "cp $metadataFiles/lean-toolchain project/"
            "cd project"
            "export PATH=\"$leanToolchainRaw/bin:${pkgs.git}/bin:${pkgs.curl}/bin:\$PATH\""
            "export LEAN_SYSROOT=\"$leanToolchainRaw\""
            # `get-` downloads the linked .ltar files without also decompressing
            # them. That keeps this fixed-output derivation focused on network
            # materialization; the ordinary derivation below does decompression.
            (runLeanCommand "$leanToolchainRaw/bin/lake exe cache get-")
          ];

          installPhase = builtins.concatStringsSep "\n" [
            "mkdir -p $out/cache/mathlib"
            "cp -r $TMPDIR/.cache/mathlib/* $out/cache/mathlib/"
            "mkdir -p $out/packages"
            "cp -r .lake/packages/* $out/packages/"
            "chmod -R +w $out/packages"
            # Drop only traces that captured Nix store paths.
            "find $out/packages -type f \\( -name \"*.trace\" -o -name \"*.hash\" \\) \\"
            "  -exec grep -q \"/nix/store\" {} \\; -delete"
            # Mathlib's build cache is reconstructed from .ltar archives below.
            "rm -rf $out/packages/mathlib/.lake"
            # Git metadata is unnecessary for path dependencies.
            "find $out/packages -type d -name \".git\" -exec rm -rf {} +"
          ];
        };

        # Unpacks Mathlib's precompiled .ltar archives.
        packages.mathlib-cache-unpacked = pkgs.stdenv.mkDerivation {
          pname = "mathlib-cache-unpacked";
          version = "0.1.0";

          src = pkgs.runCommand "empty-src" {} "mkdir $out";

          mathlibCache = self.packages.${system}.mathlib-cache-download;
          leantar = self.packages.${system}.leantar;

          nativeBuildInputs = with pkgs; [
            gnutar
            zstd
          ];

          buildPhase = builtins.concatStringsSep "\n" [
            "mkdir -p $out/packages"
            "cp -r $mathlibCache/packages/* $out/packages/"
            "chmod -R +w $out/packages"
            # Lean v4.30.0-rc2's linux_aarch64 archive accidentally bundles an
            # x86_64 `leantar`, so do not rely on the Lean toolchain copy here.
            # Fetch the matching native `leantar` release directly instead.
            "LEANTAR_BIN=\"$leantar/bin/leantar\""
            "if [ ! -x \"\$LEANTAR_BIN\" ]; then"
            "  echo \"ERROR: leantar utility binary not found at \$LEANTAR_BIN!\""
            "  exit 1"
            "fi"
            "echo \"Using leantar binary at: \$LEANTAR_BIN\""
            # Each archive expands into the project-wide .lake/build tree.
            "find $mathlibCache/cache/mathlib -name \"*.ltar\" -print0 | \\"
            "  xargs -0 -n 1 -P 48 bash -c \"\$LEANTAR_BIN -d -C $out \\\"\\\$0\\\"\""
            # Keep the release archive reproducible.
            "find $out -exec touch -h -d \"1970-01-01 00:00:00\" {} +"
          ];
        };

        # One immutable, Lean-artifact-free tree supplies identical rewritten
        # sources, package topology, metadata, mtimes, and runtime tools to both
        # build modes. ProofWidgets' pre-generated JavaScript and its two
        # custom-target traces are source inputs; the slow builder never
        # receives the candidate `.lake` seed below.
        packages.aeneas-prepared-sources = pkgs.stdenv.mkDerivation ({
          pname = "aeneas-prepared-sources";
          version = "0.1.0";

          dontPatchShebangs = true;
          dontPatchELF = true;
          dontStrip = true;

          src = pkgs.runCommand "empty-src" {} "mkdir $out";
          aeneasUnpacked = self.packages.${system}.aeneas-unpacked;
          mathlibSources = self.packages.${system}.mathlib-cache-download;

          nativeBuildInputs = with pkgs; [ python3 ];

          buildPhase = builtins.concatStringsSep "\n" [
            "mkdir -p $out/backends $out/packages $out/bin"
            "cp -r $aeneasUnpacked/backends/lean $out/backends/"
            "cp -r $mathlibSources/packages/* $out/packages/"
            "cp \$(find $aeneasUnpacked -maxdepth 1 -type f -executable) $out/bin/"
            "chmod -R +w $out"
            # Delete every candidate artifact before the common cut point.
            "find $out -type d \\( -name .lake -o -name .git \\) -prune -exec rm -rf {} +"
            "python3 ${./rewrite-lake-vendor.py} --root $out/backends/lean --packages-dir $out/packages"
            "find $out -exec touch -h -d '1970-01-01 00:00:00' {} +"
            "if find $out -type d -name .lake -print -quit | grep -q .; then"
            "  echo \"ERROR: prepared sources still contain a .lake directory\" >&2"
            "  exit 1"
            "fi"
            "if find $out -type f \\( -name '*.hash' -o -name '*.olean' -o -name '*.ilean' -o -name '*.ltar' \\) -print -quit | grep -q .; then"
            "  echo \"ERROR: prepared sources still contain a Lake build artifact\" >&2"
            "  exit 1"
            "fi"
            "if find $out -type f -name '*.trace' ! -path \"$out/packages/proofwidgets/widget/package-lock.json.trace\" ! -path \"$out/packages/proofwidgets/widget/js/lake.trace\" -print -quit | grep -q .; then"
            "  echo \"ERROR: prepared sources contain an unexpected non-.lake trace\" >&2"
            "  exit 1"
            "fi"
            "if grep -RFl -e \"$aeneasUnpacked\" -e \"$mathlibSources\" $out >/tmp/prepared-store-paths; then"
            "  echo \"ERROR: prepared sources retain input-store paths\" >&2"
            "  cat /tmp/prepared-store-paths >&2"
            "  exit 1"
            "fi"
          ];
        } // pkgs.lib.optionalAttrs pkgs.stdenv.isDarwin {
          # nixpkgs' Darwin fixup hook otherwise rewrites every cached
          # `.dylib`/`.so` after Lake records its content hash.
          preFixup = ''
            fixDarwinDylibNamesIn() { :; }
          '';
        });

        # Candidate `.lake` state is isolated from the shared source output.
        # Only the fast builder has this derivation in its input graph.
        packages.aeneas-prepared-cache = pkgs.stdenv.mkDerivation ({
          pname = "aeneas-prepared-cache";
          version = "0.1.0";

          dontPatchShebangs = true;
          dontPatchELF = true;
          dontStrip = true;

          src = pkgs.runCommand "empty-src" {} "mkdir $out";
          aeneasUnpacked = self.packages.${system}.aeneas-unpacked;
          mathlibCache = self.packages.${system}.mathlib-cache-unpacked;

          buildPhase = builtins.concatStringsSep "\n" [
            "mkdir -p $out/backends/lean $out/packages"
            "cp -r $aeneasUnpacked/backends/lean/.lake $out/backends/lean/"
            "for package_dir in $mathlibCache/packages/*; do"
            "  package_name=\$(basename \"$package_dir\")"
            "  if [ -d \"$package_dir/.lake\" ]; then"
            "    mkdir -p \"$out/packages/$package_name/.lake\""
            "    cp -r \"$package_dir/.lake/.\" \"$out/packages/$package_name/.lake/\""
            "  fi"
            "done"
            "mkdir -p $out/packages/mathlib/.lake"
            "cp -r $mathlibCache/.lake/build $out/packages/mathlib/.lake/"
            "chmod -R +w $out"
            "if [ -d $mathlibCache/.lake/packages ]; then"
            "  for cached_pkg in $mathlibCache/.lake/packages/*; do"
            "    package_name=\$(basename \"$cached_pkg\")"
            "    if [ -d \"$cached_pkg/.lake\" ]; then"
            "      mkdir -p \"$out/packages/$package_name/.lake\""
            "      cp -r \"$cached_pkg/.lake/.\" \"$out/packages/$package_name/.lake/\""
            "    fi"
            "  done"
            "fi"
            # A clean build records reference usages from `...? ... says ...`
            # terms that these two candidate `.ilean` files omit. Their
            # `.olean` files are byte-identical to the clean result. Leave just
            # the stale code-intelligence outputs absent so the fast build
            # regenerates them while replaying the rest of the candidate cache.
            "for ilean in backends/lean/.lake/build/lib/lean/Aeneas/Tactic/Step/Step.ilean packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic/NormNum/Ineq.ilean; do"
            "  rm -f \"$out/$ilean\" \"$out/$ilean.hash\""
            "done"
            "test -f $out/packages/batteries/.lake/build/lib/lean/Batteries/Data/Array/Merge.olean"
            "if find $out -type f ! -path '*/.lake/*' -print -quit | grep -q .; then"
            "  echo \"ERROR: prepared cache contains a file outside .lake\" >&2"
            "  exit 1"
            "fi"
          ];
        } // pkgs.lib.optionalAttrs pkgs.stdenv.isDarwin {
          preFixup = ''
            fixDarwinDylibNamesIn() { :; }
          '';
        });

        packages.aeneas-compiled-fast = buildAeneas {
          mode = "fast";
          prepared = self.packages.${system}.aeneas-prepared-sources;
          seed = self.packages.${system}.aeneas-prepared-cache;
        };

        packages.aeneas-compiled-slow = buildAeneas {
          mode = "slow";
          prepared = self.packages.${system}.aeneas-prepared-sources;
        };

        # Existing users and releases retain the efficient implementation.
        packages.aeneas-compiled = self.packages.${system}.aeneas-compiled-fast;

        # Stages the relocatable toolchain bundle before compression.
        packages.omnibus-tar-fast = pkgs.stdenv.mkDerivation {
          pname = "anneal-toolchain-omnibus-tar-fast";
          version = "0.1.0";

          src = pkgs.runCommand "empty-src" {} "mkdir $out";

          nativeBuildInputs = with pkgs; [
            gnutar
          ] ++ pkgs.lib.optionals stdenv.isLinux [
            patchelf
            file
          ];

          aeneasBuild = self.packages.${system}.aeneas-compiled-fast;
          rustToolchain = self.packages.${system}.rust-toolchain;
          leanToolchain = self.packages.${system}.lean-toolchain;

          buildPhase = builtins.concatStringsSep "\n" ([
            "mkdir -p $TMPDIR/dist_staging"
            "chmod -R +w $TMPDIR/dist_staging/"
            "mkdir -p $TMPDIR/dist_staging/lean"
            "cp -r $leanToolchain/* $TMPDIR/dist_staging/lean/"
            "chmod -R +w $TMPDIR/dist_staging/lean"
            "mkdir -p $TMPDIR/dist_staging/rust"
            "cp -r $rustToolchain/* $TMPDIR/dist_staging/rust/"
            "chmod -R +w $TMPDIR/dist_staging/rust"
            "mkdir -p $TMPDIR/dist_staging/aeneas"
            "cp -r $aeneasBuild/* $TMPDIR/dist_staging/aeneas/"
            "chmod -R +w $TMPDIR/dist_staging/aeneas"
            # Setup descriptions are compiler invocation scratch files. Three
            # upstream Batteries cache entries also retain export lists that a
            # clean build no longer produces; other export lists are required
            # by AeneasMeta's native closure and must remain in the archive.
            "find $TMPDIR/dist_staging/aeneas -type f -name '*.setup.json' -delete"
            "for export in Batteries/Data/Array/Match Batteries/Data/String/Basic Batteries/Data/String/Matcher; do"
            "  rm -f \"$TMPDIR/dist_staging/aeneas/packages/batteries/.lake/build/ir/$export.c.o.export\""
            "  rm -f \"$TMPDIR/dist_staging/aeneas/packages/batteries/.lake/build/ir/$export.c.o.export.hash\""
            "done"
          ] ++ pkgs.lib.optionals pkgs.stdenv.isLinux [
            # Remove Nix dynamic-linker and RPATH references from ELF binaries.
            "echo \"Cleaning up Nix store references...\""
            # Cached Lake artifacts were hashed by `aeneas-compiled`; mutating
            # them here would make the read-only archive fail hash-mode IDE
            # setup. They are already relocatable, so normalize only runtime
            # and toolchain executables.
            "find $TMPDIR/dist_staging -type f -executable ! -path \"$TMPDIR/dist_staging/aeneas/*/.lake/*\" | while read -r file; do"
            "  if file \"\$file\" | grep -q \"ELF 64-bit\"; then"
            "    echo \"Patching and stripping \$file...\""
            "    if patchelf --print-interpreter \"\$file\" >/dev/null 2>&1; then"
            "      patchelf --set-interpreter ${linuxDynamicLinker} \"\$file\" || true"
            "    fi"
            "    patchelf --set-rpath \"\" \"\$file\" || true"
            "    strip \"\$file\" || true"
            "  fi"
            "done"
          ] ++ [
            "TRACE_ABS_RE='(^|[\"[:space:]=:])/[A-Za-z0-9._~-]'"
            "if find $TMPDIR/dist_staging -type f -name \"*.trace\" -exec grep -EIl \"\$TRACE_ABS_RE\" {} + | tee /tmp/non-relocatable-staged-traces | grep -q .; then"
            "  echo \"ERROR: non-relocatable paths remain in staged Lake trace files\" >&2"
            "  cat /tmp/non-relocatable-staged-traces >&2"
            "  exit 1"
            "fi"
            # FIXME: Figure out whether v2 can avoid this mtime workaround.
            # Nix store finalization and the staging copy can collapse file
            # mtimes in the final archive. Keep Lake source/config inputs
            # older than the prebuilt `.lake/build` artifacts so generated v1
            # workspaces can use `lake --old` against the installed archive
            # without setup-time mtime repair.
            "find $TMPDIR/dist_staging/aeneas -type f \\( -name \"*.lean\" -o -name \"lakefile.lean\" -o -name \"lakefile.toml\" -o -name \"lake-manifest.json\" -o -name \"lean-toolchain\" \\) -exec touch -h -d \"1970-01-01 00:00:00\" {} +"
            "chmod -R a-w $TMPDIR/dist_staging"
            "cd $TMPDIR/dist_staging"
            "tar -cf $out *"
          ]);
        };

        packages.omnibus-tar-slow = self.packages.${system}.omnibus-tar-fast.overrideAttrs (_: {
          pname = "anneal-toolchain-omnibus-tar-slow";
          aeneasBuild = self.packages.${system}.aeneas-compiled-slow;
        });

        packages.omnibus-tar = self.packages.${system}.omnibus-tar-fast;

        # Final compressed toolchain archive. This is the local-development
        # default, so keep compression fast.
        packages.omnibus-archive-fast = pkgs.stdenv.mkDerivation {
          pname = "anneal-toolchain-omnibus-fast";
          version = "0.1.0";

          src = pkgs.runCommand "empty-src" {} "mkdir $out";

          nativeBuildInputs = with pkgs; [
            zstd
          ];

          omnibusTar = self.packages.${system}.omnibus-tar-fast;

          ANNEAL_ZSTD_LEVEL = 1;

          buildPhase = builtins.concatStringsSep "\n" [
            "ZSTD_LEVEL=\${ANNEAL_ZSTD_LEVEL:-1}"
            "echo \"Compressing with Zstd level \$ZSTD_LEVEL...\""
            "zstd -\$ZSTD_LEVEL $omnibusTar -o $out"
          ];
        };

        packages.omnibus-archive-slow = self.packages.${system}.omnibus-archive-fast.overrideAttrs (_: {
          pname = "anneal-toolchain-omnibus-slow";
          omnibusTar = self.packages.${system}.omnibus-tar-slow;
        });

        packages.omnibus-archive = self.packages.${system}.omnibus-archive-fast;

        # CI caches this archive across runs, so use a moderate compression
        # level that keeps cache/artifact size under control without making
        # from-scratch PR rebuilds pay the level-19 CPU cost.
        packages.omnibus-archive-ci-fast = self.packages.${system}.omnibus-archive-fast.overrideAttrs (_: {
          ANNEAL_ZSTD_LEVEL = 6;
        });

        packages.omnibus-archive-ci-slow = self.packages.${system}.omnibus-archive-slow.overrideAttrs (_: {
          ANNEAL_ZSTD_LEVEL = 6;
        });

        packages.omnibus-archive-ci = self.packages.${system}.omnibus-archive-ci-fast;

        packages.omnibus-archive-layout-check-fast =
          pkgs.runCommand "anneal-toolchain-omnibus-layout-check" {
            nativeBuildInputs = with pkgs; [
              gnutar
              zstd
            ];

            archive = self.packages.${system}.omnibus-archive-ci-fast;
          } ''
            set -euo pipefail

            mkdir -p "$TMPDIR/archive"
            zstd -dc "$archive" | tar -tf - > "$TMPDIR/archive/entries"

            cut -d/ -f1 "$TMPDIR/archive/entries" | sort -u > "$TMPDIR/archive/top-level"
            cat > "$TMPDIR/archive/expected-top-level" <<EOF
            aeneas
            lean
            rust
            EOF
            if ! diff -u "$TMPDIR/archive/expected-top-level" "$TMPDIR/archive/top-level"; then
              echo "ERROR: unexpected top-level archive layout" >&2
              exit 1
            fi

            for path in \
              aeneas/bin/aeneas \
              aeneas/bin/charon \
              aeneas/bin/charon-driver \
              aeneas/backends/lean/.lake/config/aeneas/lakefile.olean \
              aeneas/backends/lean/lakefile.lean \
              aeneas/packages/mathlib/lake-manifest.json \
              aeneas/packages/mathlib/.lake/config/mathlib/lakefile.olean \
              lean/bin/lean \
              rust/bin/cargo \
              rust/bin/rustc; do
              if ! grep -Fxq "$path" "$TMPDIR/archive/entries"; then
                echo "ERROR: expected archive entry missing: $path" >&2
                exit 1
              fi
            done

            if ! grep -Eq '^aeneas/packages/mathlib/\.lake/build/lib/lean/Mathlib/.+\.olean$' "$TMPDIR/archive/entries"; then
              echo "ERROR: archive is missing Mathlib .olean cache artifacts" >&2
              exit 1
            fi

            if grep -E '(^/|(^|/)\.\.(/|$))' "$TMPDIR/archive/entries"; then
              echo "ERROR: archive contains absolute or parent-relative paths" >&2
              exit 1
            fi

            if grep -E '^(anneal|v2|exocrate)(/|$)' "$TMPDIR/archive/entries"; then
              echo "ERROR: archive appears to contain repository checkout paths" >&2
              exit 1
            fi

            mkdir -p "$out"
            cp "$TMPDIR/archive/entries" "$out/entries"
          '';

        packages.omnibus-archive-layout-check-slow =
          self.packages.${system}.omnibus-archive-layout-check-fast.overrideAttrs (_: {
            name = "anneal-toolchain-omnibus-layout-check-slow";
            archive = self.packages.${system}.omnibus-archive-ci-slow;
          });

        packages.omnibus-archive-layout-check =
          self.packages.${system}.omnibus-archive-layout-check-fast;

        packages.rust-toolchain = fetchRustToolchain {
          inherit rustDate;
          sha256 = rustToolchainSha256;
        };

        packages.lean-toolchain = fetchLeanToolchain {
          inherit leanVersion;
          sha256 = leanToolchainSha256;
        };

        packages.leantar = fetchLeantar {
          version = "0.1.16";
          sha256 = leantarSha256;
        };

        # Verifies that Aeneas metadata can drive toolchain derivations.
        packages.test-ifd =
          let
            unpacked = self.packages.${system}.aeneas-unpacked;

            aeneasMetadata = builtins.fromJSON (builtins.readFile "${unpacked}/metadata.json");

            leanVersion = aeneasMetadata.lean-toolchain;
            rustVersion = aeneasMetadata.rust-toolchain-version;
            rustDate = aeneasMetadata.rust-toolchain-date;

            dynamicRust = fetchRustToolchain {
              inherit rustDate;
              sha256 = self.packages.${system}.rust-toolchain.outputHash;
            };

            dynamicLean = fetchLeanToolchain {
              inherit leanVersion;
              sha256 = self.packages.${system}.lean-toolchain.outputHash;
            };
          in
          pkgs.runCommand "test-ifd-eval" {} (builtins.concatStringsSep "\n" [
            "echo \"Dynamic IFD Verification Success!\""
            "echo \"Extracted Lean Toolchain Version: ${leanVersion}\""
            "echo \"Extracted Rust Toolchain Version: ${rustVersion}\""
            "echo \"Dynamically Constructed Rust Toolchain Store Path: ${dynamicRust}\""
            "echo \"Dynamically Constructed Lean Toolchain Store Path: ${dynamicLean}\""
            "test -f ${dynamicRust}/bin/rustc"
            "test -f ${dynamicLean}/bin/lean"
            "echo \"Lean: ${leanVersion}, Rust: ${rustVersion}\" > $out"
            "echo \"Wired Rust Toolchain: ${dynamicRust}\" >> $out"
            "echo \"Wired Lean Toolchain: ${dynamicLean}\" >> $out"
          ]);

        packages.default = self.packages.${system}.aeneas-unpacked;
      });
}
