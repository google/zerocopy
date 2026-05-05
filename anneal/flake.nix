{
  description = "Clean Aeneas Downloader Derivation";

  # External dependencies (repositories) consumed by this Flake.
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  # Outputs defines the packages, shells, and functions this Flake exposes.
  # It takes the evaluated inputs as arguments.
  outputs = { self, nixpkgs, flake-utils, ... }:
    # Nix packages are system-architecture dependent (e.g. x86_64-linux,
    # aarch64-darwin). `eachDefaultSystem` automatically loops through all
    # common CPU architectures, nesting our package output definitions under
    # their corresponding system name (e.g., `packages.x86_64-linux.default`),
    # keeping our configuration clean and DRY.
    flake-utils.lib.eachDefaultSystem (system:
      let
        # legacyPackages provides the package set for the current target system.
        pkgs = nixpkgs.legacyPackages.${system};

        # Centralized platform target resolving maps.
        # Maps standard Nix systems (e.g., x86_64-linux) to upstream triple naming.
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

        # Parameterized helper function to download the prebuilt Aeneas release
        # archive.
        #
        # In Nix, all builds run in a highly restricted, network-free sandbox.
        # To download files, we use Fixed-Output Derivations (FODs), such as
        # `pkgs.fetchurl`. An FOD is allowed network access because its output
        # is cryptographically locked to a pre-declared checksum (`sha256`).
        # If the downloaded file's hash differs, Nix aborts the build.
        fetchAeneas = { target, releaseTag, sha256 }:
          pkgs.fetchurl {
            name = "aeneas-${target}.tar.gz";
            url = "https://github.com/AeneasVerif/aeneas/releases/download/${releaseTag}/aeneas-${target}.tar.gz";
            inherit sha256;
          };

        # A generic helper function that creates a hermetic, relocatable,
        # fixed-output derivation (FOD) with internet access.
        # It encapsulates all shared parameters and security overrides (bypassing
        # automatic shebang/ELF patchers to prevent Nix store path reference leaks).
        fetchToolchainAsset = { pname, version, sha256, buildPhase }:
          pkgs.stdenv.mkDerivation {
            inherit pname version sha256 buildPhase;

            dontUnpack = true;

            # Disable Nix's automatic post-install patchers (shebang rewrites,
            # ELF dynamic linker patching, and binary stripping) to prevent
            # leaking dynamic builder store paths (like bash) into output files.
            dontPatchShebangs = true;
            dontPatchELF = true;
            dontStrip = true;

            outputHashMode = "recursive";
            outputHashAlgo = "sha256";
            outputHash = sha256;

            # Merged set of build-time tools required by all downloader scripts
            nativeBuildInputs = with pkgs; [
              curl
              cacert
              gnutar
              gzip
              zstd
            ];

            # Configure certificate bundle for secure dynamic downloads
            SSL_CERT_FILE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";
          };

        # Parameterized helper function to download and merge the 6 Rust
        # toolchain components into a single unified compiler directory (sysroot).
        fetchRustToolchain = { rustDate, sha256 }:
          fetchToolchainAsset {
            pname = "rust-toolchain";
            version = rustDate;
            inherit sha256;

            buildPhase = ''
              mkdir -p $out
              
              # A local bash helper function to download and extract a nightly
              # component.
              #
              # Escaping Note: In Nix, multiline strings are declared using
              # two consecutive single quotes. Nix uses standard dollar-brace
              # syntax for Nix-level string interpolation. To write a literal
              # dollar-brace for bash (like the name variable), we must escape
              # the dollar sign using two single quotes. Un-escaped references
              # (like the rustDate variable) are dynamically interpolated by
              # Nix during evaluation.
              extract_component() {
                local name=$1
                local url="https://static.rust-lang.org/dist/${rustDate}/''${name}-nightly-${rustPlatform}.tar.gz"
                echo "Downloading and extracting $name from $url..."
                
                mkdir -p tmp_extract
                curl -sSL "$url" | tar -xz -C tmp_extract
                
                local top_dir=$(ls tmp_extract | head -n 1)
                # Resolve the component directory path nested inside top_dir
                # (e.g. 'tmp_extract/rustc-nightly-x86_64-unknown-linux-gnu/rustc')
                # This perfectly replicates setup.rs double-directory skipping.
                local comp_dir=$(find "tmp_extract/$top_dir" -mindepth 1 -maxdepth 1 -type d | head -n 1)
                
                cp -r $comp_dir/* $out/
                rm -rf tmp_extract
              }

              # 1. Extract standard platform components
              extract_component "rustc"
              extract_component "rust-std"
              extract_component "rustc-dev"
              extract_component "llvm-tools"
              extract_component "miri"

              # 2. Extract target-independent rust-src separately
              echo "Downloading and extracting rust-src..."
              mkdir -p tmp_extract
              curl -sSL "https://static.rust-lang.org/dist/${rustDate}/rust-src-nightly.tar.gz" | tar -xz -C tmp_extract
              local top_dir=$(ls tmp_extract | head -n 1)
              cp -r tmp_extract/$top_dir/rust-src/* $out/
              rm -rf tmp_extract
            '';
          };

        # Parameterized helper function to download and extract the Lean compiler toolchain
        fetchLeanToolchain = { leanVersion, sha256 }:
          let
            # Dynamically normalize the version string (strip any leading "v" if present)
            # e.g. "v4.28.0-rc1" -> "4.28.0-rc1"
            rawVersion = if builtins.substring 0 1 leanVersion == "v"
                         then builtins.substring 1 (builtins.stringLength leanVersion - 1) leanVersion
                         else leanVersion;
          in
          fetchToolchainAsset {
            pname = "lean-toolchain";
            version = rawVersion;
            inherit sha256;

            buildPhase = ''
              mkdir -p $out
              
              url="https://releases.lean-lang.org/lean4/${leanVersion}/lean-${rawVersion}-${leanPlatform}.tar.zst"
              echo "Downloading Lean toolchain from $url..."
              
              # Download and extract the .tar.zst archive directly to $out
              # We strip the first directory component (e.g. 'lean-4.28.0-rc1-linux/')
              # so the inner 'bin/', 'lib/', 'share/' subdirectories sit directly under $out.
              curl -sSL "$url" | zstd -d | tar -x -C $out --strip-components=1
            '';
          };
      in
      {
        packages.aeneas-download-linux-x86_64 = fetchAeneas {
          target = "linux-x86_64";
          releaseTag = "build-2026.04.07.112215-42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4";
          sha256 = "a448682a154590e65b0794c42487583352375fc04bdd6b2418324f6ecafcc94f";
        };

        # A standard, offline derivation that unpacks the downloaded Aeneas
        # archive and extracts expected toolchain versions inside the sandbox.
        #
        # It takes Aeneas downloader as its input dependency (`src`). Nix
        # automatically builds the downloader first and makes the output store
        # path available as the `$src` environment variable.
        packages.aeneas-unpacked = pkgs.stdenv.mkDerivation {
          pname = "aeneas-unpacked";
          version = "1.0.0";

          src = self.packages.${system}.aeneas-download-linux-x86_64;

          nativeBuildInputs = with pkgs; [
            gnutar
            gzip
            binutils  # Provides `strings` utility
          ];

          dontUnpack = true;

          buildPhase = ''
            # 1. Unpack the downloaded archive directly into output directory
            mkdir -p $out
            tar -xzf $src -C $out
            chmod -R +w $out

            # 2. Extract Lean version from unpacked toolchain file
            LEAN_RAW=$(cat $out/backends/lean/lean-toolchain)
            LEAN_VERSION=$(echo "$LEAN_RAW" | sed -E 's|leanprover/lean4:v?||' | tr -d '\n')

            # 3. Extract Rust nightly version date from precompiled charon binary.
            #
            # Why: Every Rust binary compiled with rustc embeds its compiler's
            # version signature, containing the commit date (e.g., '2026-02-06').
            # We extract the commit date using `strings` and `grep`, and then
            # calculate the corresponding nightly toolchain release date (which
            # is always the day after the commit date) using the standard `date`
            # command. This avoids reliance on Nix-specific builder store paths.
            #
            # FIXME: While `strings` is portable across guest architectures,
            # parsing compiled binary signatures is unstable. If upstream Aeneas
            # or Charon changes its compiler version signature format or strips
            # the binary in the future, this regex will fail.
            #
            # A more robust alternative would be:
            # 1. Fetch Aeneas's 'charon-pin' file from GitHub to get Charon's
            #    commit hash.
            # 2. Fetch Charon's 'charon/rust-toolchain' file from GitHub at that
            #    commit to read the TOML nightly version date in plain text.
            #
            # However, that requires fetching multiple external files with
            # separate pre-declared output hashes in Nix. For now, `strings`
            # is sufficient.
            COMMIT_DATE=$(strings $out/charon | grep -o "rustc version .* ([0-9a-f]\{9\} [0-9]\{4\}-[0-9]\{2\}-[0-9]\{2\})" | head -n 1 | grep -o "[0-9]\{4\}-[0-9]\{2\}-[0-9]\{2\}" | tr -d '\n')
            RUST_DATE=$(date -d "$COMMIT_DATE + 1 day" +%Y-%m-%d)
            RUST_VERSION="nightly-$RUST_DATE"

            # 4. Write metadata.json to the output path
            cat <<EOF > $out/metadata.json
{
  "lean-toolchain": "$LEAN_VERSION",
  "rust-toolchain-date": "$RUST_DATE",
  "rust-toolchain-version": "$RUST_VERSION"
}
EOF
          '';
        };

        # Exposes a narrow derivation that only extracts the metadata configuration
        # files from the prebuilt Aeneas release archive. This decouples the subsequent
        # Mathlib cache download from binary toolchain packaging modifications.
        packages.aeneas-metadata-files = pkgs.stdenv.mkDerivation {
          pname = "aeneas-metadata-files";
          version = "1.0.0";

          src = self.packages.${system}.aeneas-download-linux-x86_64;

          nativeBuildInputs = with pkgs; [
            gnutar
            gzip
          ];

          dontUnpack = true;

          buildPhase = ''
            mkdir -p $out
            # Extract only the three target metadata files from the tarball
            tar -xzf $src -C $out --strip-components=2 \
              backends/lean/lakefile.lean \
              backends/lean/lake-manifest.json \
              backends/lean/lean-toolchain
          '';
        };

        # Downloads the precompiled Mathlib CDN cache files from Azure inside a
        # narrowly-scoped Fixed-Output Derivation (FOD). It depends solely on static
        # compiler and metadata inputs to decouple the network download phase from active
        # relocatable toolchain packaging development.
        packages.mathlib-cache-download = pkgs.stdenv.mkDerivation {
          pname = "mathlib-cache-download";
          version = "0.1.0";

          dontUnpack = true;

          # Disable Nix dynamic shebang and ELF patchers to prevent dynamic builder leaks
          dontPatchShebangs = true;
          dontPatchELF = true;
          dontStrip = true;

          # Fixed-output configuration to allow sandboxed network access
          outputHashMode = "recursive";
          outputHashAlgo = "sha256";
          outputHash = "sha256-YBAHHLavdDQMeGI8jFhf8lJlwDzTe+R8QyZLqwXSyRg=";

          # Narrow inputs
          leanToolchainRaw = self.packages.${system}.lean-toolchain;
          metadataFiles = self.packages.${system}.aeneas-metadata-files;

          nativeBuildInputs = with pkgs; [
            git
            steam-run
            gnutar
            zstd
            curl
            cacert
          ];

          SSL_CERT_FILE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";

          buildPhase = ''
            export HOME=$TMPDIR
            
            # 1. Reconstruct the synthetic minimal project using narrow configuration files.
            mkdir -p project
            cp $metadataFiles/lakefile.lean project/
            cp $metadataFiles/lake-manifest.json project/
            cp $metadataFiles/lean-toolchain project/
            cd project

            # 2. Run lake exe cache get inside steam-run using the raw compiler
            export PATH="${pkgs.git}/bin:${pkgs.curl}/bin:$PATH"
            steam-run $leanToolchainRaw/bin/lake exe cache get
          '';

          installPhase = ''
            # 1. Copy the downloaded .ltar cache files from ~/.cache/mathlib/
            mkdir -p $out/cache/mathlib
            cp -r $TMPDIR/.cache/mathlib/* $out/cache/mathlib/

            # 2. Copy the resolved package checkouts cloned by Lake
            mkdir -p $out/packages
            cp -r .lake/packages/* $out/packages/
            chmod -R +w $out/packages

            # 3. Scrub only compiler metadata files that leak store references.
            #
            # Why: During package resolution, Lake writes `.trace` and `.hash` files.
            # Some of these (like `ProofWidgets` JS asset traces) do not contain compiler
            # paths and are necessary for offline builds. We surgically delete ONLY 
            # the `.trace` and `.hash` files that actually contain Nix store paths, 
            # preserving all clean package asset traces perfectly.
            find $out/packages -type f \( -name "*.trace" -o -name "*.hash" \) \
              -exec grep -q "/nix/store" {} \; -delete

            # 4. Scrub the entire Mathlib build directory.
            #
            # Why: Mathlib compiled object directories are massive. Since we reconstruct
            # Mathlib's build cache offline in Layer 2 by unpacking clean `.ltar` archives, 
            # we can safely delete Mathlib's `.lake` folder entirely to save space while 
            # preserving the `.lake/` folder (and precompiled JS assets) for other packages.
            rm -rf $out/packages/mathlib/.lake

            # 5. Git Scrubbing recursively to guarantee 100% deterministic bit-identity
            #
            # FIXME: It may later turn out that we need to preserve `.git`; if this is the case, 
            # we may want to explore mocking the system time (e.g., via libfaketime) to make `.git`'s 
            # contents deterministic.
            find $out/packages -type d -name ".git" -exec rm -rf {} +
          '';
        };

        # Extracts the precompiled Mathlib .ltar bytecode archives offline. It operates
        # entirely inside the sandboxed build environment, using Aeneas's packaged
        # leantar utility to decompress all archives directly into the package checkouts.
        packages.mathlib-cache-unpacked = pkgs.stdenv.mkDerivation {
          pname = "mathlib-cache-unpacked";
          version = "0.1.0";

          src = pkgs.runCommand "empty-src" {} "mkdir $out";

          mathlibCache = self.packages.${system}.mathlib-cache-download;

          nativeBuildInputs = with pkgs; [
            gnutar
            zstd
          ];

          buildPhase = ''
            # 1. Copy the clean, git-scrubbed package directories to the output path.
            mkdir -p $out/packages
            cp -r $mathlibCache/packages/* $out/packages/
            chmod -R +w $out/packages

            # 2. Locate the precompiled leantar binary inside the cache
            LEANTAR_BIN=$(find $mathlibCache/cache/mathlib -name "leantar-*" -type f -executable | head -n 1)
            if [ -z "$LEANTAR_BIN" ]; then
              echo "ERROR: leantar utility binary not found in mathlib cache!"
              exit 1
            fi
            echo "Using leantar binary at: $LEANTAR_BIN"

            # 3. Unpack all downloaded .ltar archives recursively using leantar.
            #
            # Why: Lake precompiled dependency object files reside in .ltar archives.
            # Instead of executing the `lake` compiler (which expects .git folders and
            # triggers impure clones in the sandbox), we execute the precompiled
            # `leantar` tool to extract all archives. Because each .ltar archive preserves
            # the entire relative path structure starting from `.lake/build/`, extracting
            # them at the output root ($out) correctly populates the project-wide, global
            # `.lake/build` directory as expected by the Lean compiler.
            #
            # Parallelization: We run decompression concurrently across CPU cores using
            # xargs -P to accelerate the build phase.
            find $mathlibCache/cache/mathlib -name "*.ltar" -print0 | \
              xargs -0 -n 1 -P 48 bash -c "$LEANTAR_BIN -d -C $out \"\$0\""

            # 4. Recursively normalize all file modification times (mtimes) to the Unix Epoch.
            #
            # Why: Decompression and compilation generate non-deterministic timestamps.
            # Resetting all modification times recursively guarantees that the final
            # compressed toolchain release archive remains reproducible across builds.
            find $out -exec touch -h -d "1970-01-01 00:00:00" {} +
          '';
        };

        # Exposes a standard local derivation that compiles the Aeneas Lean backend
        # library offline. It reconstructs the project workspace using the clean
        # Mathlib cache checkouts, recursively rewrites all manifests to use local
        # relative path dependencies, and compiles the Lean bytecode.
        packages.aeneas-compiled = pkgs.stdenv.mkDerivation {
          pname = "aeneas-compiled";
          version = "0.1.0";

          src = pkgs.runCommand "empty-src" {} "mkdir $out";

          leanToolchain = self.packages.${system}.lean-toolchain;
          mathlibCache = self.packages.${system}.mathlib-cache-unpacked;
          aeneasUnpacked = self.packages.${system}.aeneas-unpacked;

          nativeBuildInputs = with pkgs; [
            python3
            steam-run
            gnutar
            zstd
          ];

          buildPhase = ''
            export HOME=$TMPDIR
            export PATH="$leanToolchain/bin:$PATH"
            
            # Prepend the Lean toolchain library directories to LD_LIBRARY_PATH.
            #
            # Why: The Lean compiler binaries are dynamically linked to the Lean
            # runtime library `libleanshared.so`. The dynamic linker must be able
            # to locate this shared library when compiling executables inside the sandbox.
            export LD_LIBRARY_PATH="$leanToolchain/lib:$leanToolchain/lib/lean:$LD_LIBRARY_PATH"

            # Disable Mathlib's automatic post-update cache fetching hook.
            #
            # Why: Mathlib's `lakefile.lean` contains a `post_update` hook that
            # attempts to execute the `cache` binary utility. Since we deleted
            # this binary inside the FOD to prevent compiler wrapper leaks, the hook
            # would crash the build. Setting this variable to "1" bypasses the
            # hook cleanly.
            export MATHLIB_NO_CACHE_ON_UPDATE=1
            
            # 1. Copy Aeneas Lean project source code
            cp -r $aeneasUnpacked/backends/lean lean
            chmod -R +w lean
            cd lean
            
            # 2. Populate Mathlib package cache
            mkdir -p $TMPDIR/packages
            cp -r $mathlibCache/packages/* $TMPDIR/packages/
            chmod -R +w $TMPDIR/packages

            # 2.5. Populate the precompiled global build cache (.lake/build).
            #
            # Why: Lake compiles all object and bytecode files into a project-wide,
            # global build directory at the project root (`.lake/build/`). To ensure
            # Aeneas compiles offline without rebuilding Mathlib from scratch, we
            # copy the pre-extracted build cache directly into the workspace.
            mkdir -p .lake
            cp -r $mathlibCache/.lake/build .lake/
            chmod -R +w .lake
            
            # 3. Execute inline Python script to recursively rewrite all manifests
            # and lakefiles to use local path dependencies. This allows Lake to resolve
            # all checkouts offline from local directories directly, bypassing all Git
            # checks and preventing it from triggering dynamic clones.
            python3 << 'EOF'
import os
import json

def strict_replace(path, target, replacement):
    with open(path, 'r') as f:
        content = f.read()
    if target not in content:
        raise Exception(f"Target not found in {path}")
    if content.count(target) > 1:
        raise Exception(f"Multiple targets found in {path}")
    new_content = content.replace(target, replacement)
    with open(path, 'w') as f:
        f.write(new_content)

def rewrite_manifest(manifest_path):
    print(f"Rewriting manifest: {manifest_path}")
    with open(manifest_path, 'r') as f:
        json_data = json.load(f)
    
    if "packages" in json_data:
        new_packages = []
        for pkg in json_data["packages"]:
            name = pkg["name"]
            new_pkg = {
                "type": "path",
                "name": name,
                "dir": f"/build/packages/{name}",
                "inherited": pkg.get("inherited", False)
            }
            new_packages.append(new_pkg)
        json_data["packages"] = new_packages
        
    with open(manifest_path, 'w') as f:
        json.dump(json_data, f, indent=2)

# Rewrite Aeneas lakefile.lean (convert mathlib dependency to path)
strict_replace(
    "lakefile.lean",
    'require mathlib from git\n  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0-rc1"',
    'require mathlib from "/build/packages/mathlib"'
)

# Rewrite Mathlib lakefile.lean (convert all its nested dependencies to paths)
mathlib_lakefile = "/build/packages/mathlib/lakefile.lean"
replacements = [
    ("require \"leanprover-community\" / \"batteries\" @ git \"main\"",
     "require batteries from \"/build/packages/batteries\""),
    ("require \"leanprover-community\" / \"Qq\" @ git \"master\"",
     "require Qq from \"/build/packages/Qq\""),
    ("require \"leanprover-community\" / \"aesop\" @ git \"master\"",
     "require aesop from \"/build/packages/aesop\""),
    ("require \"leanprover-community\" / \"proofwidgets\" @ git \"v0.0.86\"",
     "require proofwidgets from \"/build/packages/proofwidgets\""),
    ("require \"leanprover-community\" / \"importGraph\" @ git \"main\"",
     "require importGraph from \"/build/packages/importGraph\""),
    ("require \"leanprover-community\" / \"LeanSearchClient\" @ git \"main\"",
     "require LeanSearchClient from \"/build/packages/LeanSearchClient\""),
    ("require \"leanprover-community\" / \"plausible\" @ git \"main\"",
     "require plausible from \"/build/packages/plausible\""),
]
for target, rep in replacements:
    strict_replace(mathlib_lakefile, target, rep)

# Rewrite Aesop lakefile.toml (convert batteries to path)
strict_replace(
    "/build/packages/aesop/lakefile.toml",
    '[[require]]\nname = "batteries"\ngit = "https://github.com/leanprover-community/batteries"\nrev = "v4.28.0-rc1"',
    '[[require]]\nname = "batteries"\npath = "/build/packages/batteries"'
)

# Rewrite ImportGraph lakefile.toml (convert Cli to path)
strict_replace(
    "/build/packages/importGraph/lakefile.toml",
    '[[require]]\nname = "Cli"\nscope = "leanprover"\nrev = "v4.28.0-rc1"',
    '[[require]]\nname = "Cli"\npath = "/build/packages/Cli"'
)

# Rewrite all manifests recursively to point to the local sandbox path checkouts
rewrite_manifest("lake-manifest.json")
for root, _, files in os.walk("/build/packages"):
    for file in files:
        if file == "lake-manifest.json":
            rewrite_manifest(os.path.join(root, file))

print("Successfully rewrote all lakefiles and manifests to use local path dependencies.")
EOF

            # 4. Compile Aeneas Lean backend offline
            # Lake resolves path checkouts directly and compiles Aeneas. This completes
            # instantly because all precompiled .olean bytecode objects are already
            # populated in our packages checkouts!
            steam-run lake build

            # 5. Structure output cleanly to match the relocatable layout:
            # - `backends/lean/` containing the fully compiled Aeneas Lean project.
            # - `packages/` containing the local packages checkouts.
            mkdir -p $out/backends/lean
            cp -r . $out/backends/lean/
            
            mkdir -p $out/packages
            cp -r $TMPDIR/packages/* $out/packages/
          '';
        };

        # Exposes a standard derivation that stages Aeneas compiled output and the
        # Rust sysroot compiler together. It clears all Nix store dynamic linker and
        # library references from the binaries, and patches compiled trace files
        # with a stable relocatable placeholder string.
        packages.omnibus-tar = pkgs.stdenv.mkDerivation {
          pname = "anneal-toolchain-omnibus-tar";
          version = "0.1.0";

          src = pkgs.runCommand "empty-src" {} "mkdir $out";

          nativeBuildInputs = with pkgs; [
            patchelf
            file
            gnutar
          ];

          leanBuild = self.packages.${system}.aeneas-compiled;
          rustToolchain = self.packages.${system}.rust-toolchain;
          leanToolchain = self.packages.${system}.lean-toolchain;
          aeneasUnpacked = self.packages.${system}.aeneas-unpacked;

          buildPhase = ''
            # 1. Recreate the staging directory layout recursively.
            #
            # Why: Since we copy from multiple read-only Nix store paths, we must
            # recursively set write permissions after each copy. Otherwise, subsequent
            # copies would crash with `Permission denied` when writing into newly created
            # read-only chroot folders.
            mkdir -p $TMPDIR/dist_staging
            
            cp -r $leanBuild/* $TMPDIR/dist_staging/
            chmod -R +w $TMPDIR/dist_staging
            
            cp -r $rustToolchain/* $TMPDIR/dist_staging/
            chmod -R +w $TMPDIR/dist_staging
            
            cp -r $leanToolchain/* $TMPDIR/dist_staging/
            chmod -R +w $TMPDIR/dist_staging

            # Copy precompiled Aeneas and Charon binaries from the unpacked release
            cp $aeneasUnpacked/aeneas $TMPDIR/dist_staging/
            cp $aeneasUnpacked/charon $TMPDIR/dist_staging/
            cp $aeneasUnpacked/charon-driver $TMPDIR/dist_staging/
            chmod -R +w $TMPDIR/dist_staging

            # 2. Un-Nixify staging binaries recursively to make them relocatable.
            #
            # Why: Executables compiled inside the sandbox (such as `charon`,
            # `charon-driver`, and `aeneas`) link dynamically to Nix store
            # libraries and use sandboxed dynamic interpreters. We patch them to
            # point their ELF interpreters to `/lib64/ld-linux-x86-64.so.2`
            # (standard FHS path), clear their dynamic RPATHs, and strip debug
            # symbols to eliminate absolute `/nix/store` path references.
            echo "Cleaning up Nix store references..."
            find $TMPDIR/dist_staging -type f -executable | while read -r file; do
              if file "$file" | grep -q "ELF 64-bit"; then
                echo "Patching and stripping $file..."
                if patchelf --print-interpreter "$file" >/dev/null 2>&1; then
                  patchelf --set-interpreter /lib64/ld-linux-x86-64.so.2 "$file" || true
                fi
                # Set relative RPATH pointing to our relocatable toolchain library folders.
                #
                # Why: Executables (such as `charon-driver`) require shared compiler
                # runtime libraries (like `librustc_driver.so`) to execute. We set their RPATH
                # to use the `$ORIGIN` dynamic linker variable, enabling them to locate
                # their shared libraries chroot-relatively regardless of the install directory.
                patchelf --set-rpath '$ORIGIN/lib:$ORIGIN/lib/lean' "$file" || true
                strip "$file" || true
              fi
            done

            # 3. Replace absolute sandbox builder path strings inside trace files.
            #
            # Why: Lake records absolute compiler paths inside `.trace` metadata
            # files. To prevent Lake from invalidating these traces and forcing
            # recompilations from scratch, we recursively scan all `.trace` files,
            # replacing absolute `/build/` paths with the stable relocatable
            # placeholder string `/ANNEAL_PLACEHOLDER_ROOT`. At setup time, the
            # client binary performs a rapid string swap with the actual install
            # path in seconds.
            echo "Inserting relocatable placeholders inside trace files..."
            find $TMPDIR/dist_staging -type f -name "*.trace" | while read -r trace_file; do
              # Replace sandbox package and lean compile folder roots
              # with the stable placeholder
              substituteInPlace "$trace_file" \
                --replace "/build/packages" "/ANNEAL_PLACEHOLDER_ROOT/packages" \
                --replace "/build/lean" "/ANNEAL_PLACEHOLDER_ROOT/backends/lean"
            done

            # 4. Tar up everything into a single uncompressed tarball
            cd $TMPDIR/dist_staging
            tar -cf $out *
          '';
        };

        # Exposes a standard derivation that compresses the uncompressed
        # omnibus-tar archive using Zstd to produce the final relocatable
        # toolchain release asset.
        #
        # Defaults to compression level 1 (fast/standard) but accepts overrides
        # via standard Nix `.overrideAttrs`.
        packages.omnibus-archive = pkgs.stdenv.mkDerivation {
          pname = "anneal-toolchain-omnibus";
          version = "0.1.0";

          src = pkgs.runCommand "empty-src" {} "mkdir $out";

          nativeBuildInputs = with pkgs; [
            zstd
          ];

          omnibusTar = self.packages.${system}.omnibus-tar;

          # Expose as a derivation attribute to allow downstream overrides
          ANNEAL_ZSTD_LEVEL = 1;

          buildPhase = ''
            # Read the overrideable zstd compression level
            ZSTD_LEVEL=''${ANNEAL_ZSTD_LEVEL:-1}
            echo "Compressing with Zstd level $ZSTD_LEVEL..."
            
            # Compress the uncompressed tar file directly to the output path $out
            zstd -$ZSTD_LEVEL $omnibusTar -o $out
          '';
        };

        # Standard sandboxed check that compiles the cargo-anneal Rust binary
        # and executes its integration tests completely offline.
        # It mounts the precompiled relocatable Zstd toolchain in the store
        # and feeds it locally via the ANNEAL_TEST_LOCAL_ARCHIVE environment variable.
        checks.integration-tests = pkgs.stdenv.mkDerivation {
          pname = "cargo-anneal-integration-tests";
          version = "0.1.0";

          # Use the Aeneas Cargo project directory as source
          src = ./.;

          nativeBuildInputs = with pkgs; [
            cargo
            rustc
            git
            zstd
            gnutar
            graphviz
            openssl
            pkg-config
            cacert
            steam-run
          ];

          buildInputs = with pkgs; [
            openssl
          ];

          # Precompiled monolithic Zstd toolchain package in the Nix store
          omnibusArchive = self.packages.${system}.omnibus-archive;

          # Set up CARGO_HOME and cache directories inside the writeable sandbox
          CARGO_HOME = "/build/.cargo";
          RUSTUP_HOME = "/build/.rustup";

          # OpenSSL package mapping for cargo pkg-config
          PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig";

          buildPhase = ''
            export HOME=$TMPDIR
            
            # Feed the absolute Nix store path of the precompiled relocatable Zstd
            # archive to the test process. The integration test harness reads this
            # variable and dynamically forwards it via `--local-archive` CLI flags.
            export ANNEAL_TEST_LOCAL_ARCHIVE="$omnibusArchive"
            
            # We must use the vendored-sources config to compile offline
            # from local crates.
            mkdir -p .cargo
            cat <<EOF > .cargo/config.toml
[source.crates-io]
replace-with = "vendored-sources"

[source.vendored-sources]
directory = "vendor"
EOF

            # Run cargo test offline inside the hermetic sandbox!
            # We filter to only run integration tests to keep execution scoped.
            echo "Running cargo integration tests..."
            steam-run cargo test --test integration --offline -- --nocapture
          '';

          installPhase = ''
            # Checks only need to write a dummy successful output file to the store
            echo "Integration tests completed successfully!" > $out
          '';
        };









        packages.rust-toolchain = fetchRustToolchain {
          rustDate = "2026-02-07";
          sha256 = "sha256-kd/N4h5ht1tmFi3/7V4PuZgNELMYP4rZQ1dLPIx9iI0=";
        };

        # A static, standalone Lean toolchain package for direct local consumption
        packages.lean-toolchain = fetchLeanToolchain {
          leanVersion = "v4.28.0-rc1";
          sha256 = "sha256-+LuElSu93jwUhEobNekiJTMu6COmybE36S626MLcWOs=";
        };

        # Import-From-Derivation (IFD) Wiring Layer Package.
        #
        # In Nix, the evaluator is normally not allowed to read files produced
        # by builders (since builders only execute in the subsequent build
        # phase).
        #
        # IFD breaks this barrier: by calling `builtins.readFile
        # "${unpacked}/metadata.json"`, we tell the Nix evaluator to pause
        # parsing, build the `aeneas-unpacked` derivation first, read the
        # generated JSON file back into the evaluator, and bind the values to
        # native Nix variables (`leanVersion`, `rustDate`) during evaluation!
        #
        # This package demonstrates the separate "wiring" layer, dynamically
        # feeding the parsed date into both `fetchRustToolchain` AND
        # `fetchLeanToolchain` downloader helpers on the fly, with absolutely
        # zero hardcoded values.
        packages.test-ifd = 
          let
            # 1. Reference our unpacked derivation
            unpacked = self.packages.${system}.aeneas-unpacked;

            # 2. Parse metadata.json dynamically (IFD)
            aeneasMetadata = builtins.fromJSON (builtins.readFile "${unpacked}/metadata.json");

            leanVersion = aeneasMetadata.lean-toolchain;
            rustVersion = aeneasMetadata.rust-toolchain-version;
            rustDate = aeneasMetadata.rust-toolchain-date;

            # 3. Dynamically instantiate the Rust toolchain helper (IFD wiring)
            dynamicRust = fetchRustToolchain {
              inherit rustDate;
              sha256 = self.packages.${system}.rust-toolchain.outputHash;
            };

            # 4. Dynamically instantiate the Lean toolchain helper (IFD wiring)
            dynamicLean = fetchLeanToolchain {
              inherit leanVersion;
              sha256 = self.packages.${system}.lean-toolchain.outputHash;
            };
          in
          pkgs.runCommand "test-ifd-eval" {} ''
            echo "Dynamic IFD Verification Success!"
            echo "Extracted Lean Toolchain Version: ${leanVersion}"
            echo "Extracted Rust Toolchain Version: ${rustVersion}"
            echo "Dynamically Constructed Rust Toolchain Store Path: ${dynamicRust}"
            echo "Dynamically Constructed Lean Toolchain Store Path: ${dynamicLean}"
            
            # Verify the dynamic compiler binaries actually exist
            # (Cannot execute them directly due to dynamic interpreter sandbox paths)
            test -f ${dynamicRust}/bin/rustc
            test -f ${dynamicLean}/bin/lean
            
            # Write output file
            echo "Lean: ${leanVersion}, Rust: ${rustVersion}" > $out
            echo "Wired Rust Toolchain: ${dynamicRust}" >> $out
            echo "Wired Lean Toolchain: ${dynamicLean}" >> $out
          '';

        packages.default = self.packages.${system}.aeneas-unpacked;
      });
}
