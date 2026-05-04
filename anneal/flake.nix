{
  description = "Omnibus packaging for Anneal formal verification tools";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        aeneasPlatform = if system == "x86_64-linux" then "linux-x86_64"
                         else if system == "aarch64-linux" then "linux-aarch64"
                         else throw "Unsupported system: ${system}";

        rustPlatform = if system == "x86_64-linux" then "x86_64-unknown-linux-gnu"
                       else if system == "aarch64-linux" then "aarch64-unknown-linux-gnu"
                       else throw "Unsupported system: ${system}";

        aeneasHash = if system == "x86_64-linux" then "a448682a154590e65b0794c42487583352375fc04bdd6b2418324f6ecafcc94f"
                     else throw "Missing Aeneas hash for system: ${system}";

        aeneasSrc = pkgs.fetchurl {
          url = "https://github.com/AeneasVerif/aeneas/releases/download/build-2026.04.07.112215-42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4/aeneas-${aeneasPlatform}.tar.gz";
          sha256 = aeneasHash;
        };

        rustDate = "2026-02-07";

        fetchRust = name: hash: pkgs.fetchurl {
          url = "https://static.rust-lang.org/dist/${rustDate}/${name}-nightly-${rustPlatform}.tar.gz";
          sha256 = hash;
        };

        rustcSrc = fetchRust "rustc" "f58a30c9fa9add81d0e99209fd960aa429f0a4ff7a37f9044e5d9eb1a598c925";
        rustStdSrc = fetchRust "rust-std" "1b06ef4654bcacd06c4f14094ca9bfe8d8bd4129c96b6b6594e3a9cf0d0214d2";
        rustcDevSrc = fetchRust "rustc-dev" "7f120343b7153e166261558b07efb8081781cfdd617e5a59ac0e144cbbe9b3df";
        llvmToolsSrc = fetchRust "llvm-tools" "4ca90ae6805121c591bb35998c12c69e6f77f9f7cc93edd72a26dfc017f0c098";
        miriSrc = fetchRust "miri" "c90b56d0c094d6599f827b5feebb6a105af536b3540924fa373356a38f296d33";

        rustSrcSrc = pkgs.fetchurl {
          url = "https://static.rust-lang.org/dist/${rustDate}/rust-src-nightly.tar.gz";
          sha256 = "404582b3ef31783b3ee390382e149736cc5d49e5b04d4d1ac39d1371a4ddedca";
        };

        leanSrc = pkgs.fetchurl {
          url = "https://releases.lean-lang.org/lean4/v4.28.0-rc1/lean-4.28.0-rc1-linux.tar.zst";
          sha256 = "sha256-o7ATogIz9RhS6+teVJZymKN6/wVVRhcKQPHnkjS7n00=";
        };
      in
      {
        packages.default = self.packages.${system}.omnibus-archive;

        packages.lean-toolchain-patched = pkgs.stdenv.mkDerivation {
          pname = "lean-toolchain-patched";
          version = "4.28.0-rc1";

          src = leanSrc;
          
          nativeBuildInputs = with pkgs; [
            zstd
            gnutar
            patchelf
          ];

          buildPhase = ''
            mkdir -p $out
            zstd -d -c $src | tar -x -C $out --strip-components=1
            
            # Run patchelf on binaries!
            find $out/bin -type f -executable | while read -r file; do
              patchelf --set-interpreter $(cat $NIX_CC/nix-support/dynamic-linker) "$file" || true
              patchelf --set-rpath "${pkgs.stdenv.cc.cc.lib}/lib:$out/lib:$out/lib/lean" "$file" || true
            done
          '';
        };

        packages.static-assets = pkgs.stdenv.mkDerivation {
          pname = "static-assets";
          version = "0.1.0";

          src = ./.;
          
          nativeBuildInputs = with pkgs; [
            gnutar
          ];

          inherit aeneasSrc rustcSrc rustStdSrc rustcDevSrc llvmToolsSrc miriSrc rustSrcSrc;

          buildPhase = ''
            mkdir -p $out/rust
            
            extract_rust() {
              local src=$1
              local name=$2
              mkdir -p tmp_extract
              tar -xzf $src -C tmp_extract
              local top_dir=$(ls tmp_extract)
              cp -r tmp_extract/$top_dir/* $out/rust/
              rm -rf tmp_extract
            }
            
            extract_rust $rustcSrc "rustc"
            extract_rust $rustStdSrc "rust-std"
            extract_rust $rustcDevSrc "rustc-dev"
            extract_rust $llvmToolsSrc "llvm-tools"
            extract_rust $miriSrc "miri"
            
            mkdir -p tmp_extract
            tar -xzf $rustSrcSrc -C tmp_extract
            local top_dir=$(ls tmp_extract)
            cp -r tmp_extract/$top_dir/rust-src/* $out/rust/
            rm -rf tmp_extract
            
            # Extract Aeneas as well!
            mkdir -p $out/aeneas
            tar -xzf $aeneasSrc -C $out/aeneas
            chmod -R +w $out/aeneas
          '';
        };

        packages.mathlib-cache = pkgs.stdenv.mkDerivation {
          pname = "mathlib-cache";
          version = "0.1.0";

          src = ./.;

          # Disable Nix's automatic post-install patchers (shebang rewrites,
          # ELF dynamic linker patching, and binary stripping).
          #
          # Why: Nix stdenv automatically runs these in `fixupPhase` to align
          # binaries with `/nix/store/` library paths. However, in this content-
          # addressed fixed-output derivation, any absolute `/nix/store/`
          # references in the output will cause immediate store reference leak
          # failures. We disable them here and perform our own cleanups
          # manually (restoring relocatable ELFs, stripping debug symbols,
          # and clearing shebangs by removing untrusted scripts recursively).
          dontPatchShebangs = true;
          dontPatchELF = true;
          dontStrip = true;

          nativeBuildInputs = with pkgs; [
            curl
            cacert
            git
            steam-run
            elan
            gnutar
            zstd
            patchelf
            file
            binutils
          ];

          outputHashMode = "recursive";
          outputHashAlgo = "sha256";
          outputHash = "sha256-wNdiqggFuKVDAojDoUg8kUPmTaySQZyFkf3xO2olKho=";

          SSL_CERT_FILE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";

          buildPhase = ''
            export HOME=$TMPDIR
            
            # 1. Install Lean via elan
            LEAN_VERSION="leanprover/lean4:v4.28.0-rc1"
            elan default "$LEAN_VERSION"
            
            # 2. Download and extract Aeneas source (to get lakefile.lean)
            curl -L https://github.com/AeneasVerif/aeneas/releases/download/build-2026.04.07.112215-42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4/aeneas-linux-x86_64.tar.gz -o aeneas.tar.gz
            mkdir -p aeneas
            tar -xzf aeneas.tar.gz -C aeneas
            chmod -R +w aeneas
            
            cd aeneas/backends/lean
            
            # 3. Fetch Mathlib cache
            export PATH="${pkgs.curl}/bin:${pkgs.git}/bin:$PATH"
            steam-run lake exe cache get
          '';

          installPhase = ''
            # Replicate files to output store path.
            #
            # We structure the output directory cleanly into:
            # 1. `cache/mathlib/` containing the downloaded .ltar cache archives.
            # 2. `packages/` containing the resolved Lean package checkouts.
            # 3. `.elan/` containing the Lean toolchain manager environment.
            mkdir -p $out/cache/mathlib
            cp -r $TMPDIR/.cache/mathlib/* $out/cache/mathlib/
            
            # Locate Lake's packages directory recursively under the build root.
            #
            # Why: During `buildPhase`, the builder shifted CWD to compile the
            # project. Rather than using fragile relative CWD paths (which can
            # vary between stdenv phase executions), we locate `.lake/packages`
            # recursively under `$NIX_BUILD_TOP` to ensure absolute copy safety.
            PACKAGES_DIR=$(find "$NIX_BUILD_TOP" -type d -path "*/.lake/packages" | head -n 1)
            if [ -z "$PACKAGES_DIR" ]; then
              echo "ERROR: .lake/packages directory not found!"
              exit 1
            fi
            echo "Found packages directory at: $PACKAGES_DIR"
            
            mkdir -p $out/packages
            cp -r "$PACKAGES_DIR"/* $out/packages/
            chmod -R +w $out/packages
            
            # Preserve the downloaded Lean compiler environment.
            cp -r $TMPDIR/.elan $out/.elan
            chmod -R +w $out/.elan
            
            # 1. Delete Mathlib cache binary and intermediate build artifacts.
            #
            # Why: During `lake exe cache get`, Mathlib compiles its cache manager
            # utility (`cache`). This compiled binary bakes in absolute store paths.
            # Since users of the compiled prebuilt archive only need the libraries,
            # we completely delete the intermediate build output directory.
            rm -rf $out/packages/mathlib/.lake/build
            
            # 2. Scrub Git folders recursively under packages.
            #
            # Why: Git checkouts contain non-deterministic packfiles/indices due
            # to file mtimes, and Git hook templates (`.git/hooks/*.sample`) leak
            # absolute store shebangs (`#!/nix/store/.../bin/bash`).
            #
            # FIXME: It may later turn out that we need to preserve `.git`; if
            # this is the case, we may want to explore mocking the system time 
            # (e.g., via libfaketime) to make `.git`'s contents deterministic.
            find $out/packages -type d -name ".git" -exec rm -rf {} +
            
            # 3. Restore relocatable upstream Lean binaries (Scrub Nix wrappers).
            #
            # Why: When `elan` installs Lean inside the sandbox, Nix's hooks
            # replace the compiled ELF binaries (`leanc`, `lake`) with bash wrapper
            # scripts (`leanc`, `lake`, `cc`) that contain hardcoded paths to Nix's
            # GCC wrapper. These wrappers would crash on non-Nix host systems.
            #
            # We delete the wrapper scripts and rename the original relocatable
            # ELF binaries (preserved as `.orig` by the Nix installer) back to 
            # their default names, restoring the toolchain to its clean,
            # standalone, relocatable upstream state.
            ELAN_BIN_DIR=$out/.elan/toolchains/leanprover--lean4---v4.28.0-rc1/bin
            if [ -f "$ELAN_BIN_DIR/leanc.orig" ]; then
              echo "Restoring original leanc binary..."
              rm -f "$ELAN_BIN_DIR/leanc"
              mv "$ELAN_BIN_DIR/leanc.orig" "$ELAN_BIN_DIR/leanc"
            fi
            if [ -f "$ELAN_BIN_DIR/lake.orig" ]; then
              echo "Restoring original lake binary..."
              rm -f "$ELAN_BIN_DIR/lake"
              mv "$ELAN_BIN_DIR/lake.orig" "$ELAN_BIN_DIR/lake"
            fi
            echo "Deleting cc wrapper..."
            rm -f "$ELAN_BIN_DIR/cc"

            # 3.1 Replace the llvm-ar symlink with a relocatable shell script
            # wrapper.
            #
            # Why: Nix's hooks replace `llvm-ar` with a symlink pointing directly
            # to the absolute store path of the Nix GCC wrapper's `ar` binary.
            # To prevent store path leakage and ensure relocatability on host
            # systems, we replace the symlink with a shell script that simply
            # delegates to the system's standard `ar` utility in PATH.
            echo "Replacing llvm-ar symlink with relocatable host ar wrapper..."
            rm -f "$ELAN_BIN_DIR/llvm-ar"
            cat << 'EOF' > "$ELAN_BIN_DIR/llvm-ar"
#!/usr/bin/env bash
exec ar "$@"
EOF
            chmod +x "$ELAN_BIN_DIR/llvm-ar"


            # 4. Clean ELF headers and strip debug symbols from toolchain.
            #
            # We run a recursive sweep on the restored `.elan` compiler binaries
            # and dynamic libraries to make them fully stand-alone and relocatable.
            export PATH="${pkgs.patchelf}/bin:${pkgs.file}/bin:${pkgs.binutils}/bin:$PATH"
            
            clean_elf() {
              local file=$1
              # Process only regular ELF 64-bit binaries (skip symlinks).
              if [[ -f "$file" ]] && ! [[ -L "$file" ]] && file "$file" | grep -q "ELF 64-bit"; then
                chmod +w "$file"
                
                # Revert interpreter shebang to standard FHS dynamic linker path.
                if patchelf --print-interpreter "$file" >/dev/null 2>&1; then
                  echo "Patching interpreter: $file"
                  patchelf --set-interpreter /lib64/ld-linux-x86-64.so.2 "$file" || true
                fi
                
                # Revert RUNPATH (RPATH) libraries resolution.
                #
                # Why: Compiler binaries inside `bin/` must locate dynamic libs
                # shipped with the toolchain in `lib/`. To prevent leaking Nix store
                # paths, we use relative `$ORIGIN` paths (expanded dynamically
                # by `ld.so` at runtime relative to the binary's directory).
                # Dynamic libraries have their RPATH cleared as they are loaded.
                if [[ "$file" == *"/bin/"* ]]; then
                  echo "Setting relative RUNPATH: $file"
                  patchelf --set-rpath '$ORIGIN/../lib:$ORIGIN/../lib/lean:$ORIGIN/../lib/glibc' "$file" || true
                else
                  echo "Clearing RUNPATH: $file"
                  patchelf --set-rpath "" "$file" || true
                fi
                
                # Strip debugging symbols.
                #
                # Why: Compiling inside the Nix sandbox embeds absolute store
                # source paths in debug mappings, which leaks store references.
                # Running `strip` removes these debug tables cleanly.
                echo "Stripping: $file"
                strip "$file" || true
              fi
            }
            
            # Parallelize ELF cleaning across multiple CPU cores to utilize
            # host resources.
            #
            # Why: Spawning `patchelf` and `strip` sequentially for 10,000+ files
            # in a single-threaded bash loop takes several minutes. Using `xargs -P`
            # allows us to execute `clean_elf` concurrently across 48 cores,
            # shrinking this phase from minutes to seconds.
            export -f clean_elf
            find $out/.elan -type f -print0 | xargs -0 -n 1 -P 48 bash -c 'clean_elf "$0"'
            


            # 5. Reset timestamps recursively to Unix epoch
            find $out -exec touch -h -d "1970-01-01 00:00:00" {} +
          '';
        };

        packages.lean-build = pkgs.stdenv.mkDerivation {
          pname = "lean-build";
          version = "0.1.0";

          src = ./.;
          
          nativeBuildInputs = with pkgs; [
            python3
          ];
          
          leanToolchain = self.packages.${system}.lean-toolchain-patched;
          mathlibCache = self.packages.${system}.mathlib-cache;
          staticAssets = self.packages.${system}.static-assets;

          buildPhase = ''
            export HOME=$TMPDIR
            export PATH="$leanToolchain/bin:$PATH"
            # Prepend the Lean toolchain library directories to LD_LIBRARY_PATH.
            #
            # Why: The Lean compiler binaries are dynamically linked to the Lean
            # runtime library `libleanshared.so`. When executing compiled Lean
            # executables (like `graph` under importGraph) during the build, the
            # dynamic linker must be able to locate this shared library.
            export LD_LIBRARY_PATH="$leanToolchain/lib:$leanToolchain/lib/lean:$LD_LIBRARY_PATH"

            # Disable Mathlib's automatic post-update cache fetching hook.
            #
            # Why: Mathlib's `lakefile.lean` contains a `post_update` hook that
            # attempts to execute the `cache` binary utility. Since we deleted
            # this binary to prevent GCC wrapper store path leaks, the hook
            # would crash the build. Setting this variable to "1" bypasses the
            # hook cleanly.
            export MATHLIB_NO_CACHE_ON_UPDATE=1
            
            # Copy Aeneas Lean project from static-assets
            cp -r $staticAssets/aeneas/backends/lean lean
            chmod -R +w lean
            cd lean
            
            # Populate Mathlib package cache.
            #
            # Why: We structured `mathlibCache` output cleanly. The `.ltar`
            # cache archives reside under `cache/mathlib/`. Copying the entire
            # `mathlib` cache directory into `$TMPDIR/.cache/` perfectly
            # recreates `$TMPDIR/.cache/mathlib/` containing the `.ltar` files
            # as expected by Lake's cache manager.
            mkdir -p $TMPDIR/.cache
            cp -r $mathlibCache/cache/mathlib $TMPDIR/.cache/
            
            # Populate local packages registry.
            #
            # Why: We deleted `.git` directories in `mathlibCache` to ensure
            # deterministic and shebang-free outputs. As a result, Lake (which
            # expects Git repositories) fails to find `.git` and attempts to
            # re-clone them from GitHub, failing inside our sandboxed
            # network-free build environment.
            #
            # We copy the package checkouts to a writeable directory
            # `/build/packages` in $TMPDIR and run an inline Python script to
            # rewrite the dependency declarations in Aeneas and all dependency
            # lakefiles (Mathlib, Aesop, ImportGraph) to use local path
            # dependencies. This allows Lake to resolve the local directories
            # directly without checking for `.git` folders or running Git clones.
            mkdir -p /build/packages
            cp -r $mathlibCache/packages/* /build/packages/
            chmod -R +w /build/packages

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

# 1. Rewrite Aeneas lakefile.lean (convert mathlib to path)
strict_replace(
    "lakefile.lean",
    'require mathlib from git\n  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0-rc1"',
    'require mathlib from "/build/packages/mathlib"'
)

# 2. Rewrite Mathlib lakefile.lean (convert all its dependencies to paths)
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

# 3. Rewrite Aesop lakefile.toml (convert batteries to path)
strict_replace(
    "/build/packages/aesop/lakefile.toml",
    '[[require]]\nname = "batteries"\ngit = "https://github.com/leanprover-community/batteries"\nrev = "v4.28.0-rc1"',
    '[[require]]\nname = "batteries"\npath = "/build/packages/batteries"'
)

# 4. Rewrite ImportGraph lakefile.toml (convert Cli to path)
strict_replace(
    "/build/packages/importGraph/lakefile.toml",
    '[[require]]\nname = "Cli"\nscope = "leanprover"\nrev = "v4.28.0-rc1"',
    '[[require]]\nname = "Cli"\npath = "/build/packages/Cli"'
)

# 5. Rewrite all lake-manifest.json files recursively to point to path dependencies
rewrite_manifest("lake-manifest.json")
for root, _, files in os.walk("/build/packages"):
    for file in files:
        if file == "lake-manifest.json":
            rewrite_manifest(os.path.join(root, file))

print("Successfully rewrote all lakefiles and manifests to use local path dependencies.")
EOF

            lake build
            
            lake build graph:exe
            lake exe graph imports.dot
            
            # Prune Mathlib recursively based on the imports dependency graph.
            #
            # Why: Mathlib is large (~11 GB uncompressed). To reduce the final
            # archive size, we prune out all Lean modules and object files that
            # are not transitively imported by Aeneas. This shrinks Mathlib to
            # a fraction of its original size.
            python3 $src/tools/prune_mathlib.py imports.dot /build/packages/mathlib
            
            # Clean up intermediate files.
            rm imports.dot

            # Structure output cleanly to match the final prebuilt toolchain:
            # 1. `backends/lean/` containing the compiled Aeneas Lean project.
            # 2. `packages/` containing the pruned dependency checkouts.
            mkdir -p $out/backends/lean
            cp -r . $out/backends/lean/
            
            mkdir -p $out/packages
            cp -r /build/packages/* $out/packages/
          '';
        };

        packages.omnibus-tar = pkgs.stdenv.mkDerivation {
          pname = "anneal-toolchain-omnibus-tar";
          version = "0.1.0";

          src = ./.;
          
          nativeBuildInputs = with pkgs; [
            patchelf
            file
          ];
          
          staticAssets = self.packages.${system}.static-assets;
          leanBuild = self.packages.${system}.lean-build;

          buildPhase = ''
            mkdir -p $TMPDIR/dist_staging
            cp -r $leanBuild/* $TMPDIR/dist_staging/
            cp -r $staticAssets/rust $TMPDIR/dist_staging/
            
            # Revert store references and make staging binaries relocatable.
            #
            # Why: Staging executables (like `charon` and `charon-driver`) compiled
            # inside the sandbox reference Nix store libraries and dynamic linkers.
            # We un-nixify them by setting their interpreter to the standard FHS
            # path `/lib64/ld-linux-x86-64.so.2`, clearing their dynamic RPATHs,
            # and running `strip` to discard debug symbol maps referencing store
            # Rust standard library or vendor dependency paths.
            echo "Cleaning up Nix store references..."
            find $TMPDIR/dist_staging -type f -executable | while read -r file; do
              if file "$file" | grep -q "ELF 64-bit"; then
                echo "Patching and stripping $file..."
                if patchelf --print-interpreter "$file" >/dev/null 2>&1; then
                  patchelf --set-interpreter /lib64/ld-linux-x86-64.so.2 "$file" || true
                fi
                patchelf --set-rpath "" "$file" || true
                strip "$file" || true
              fi
            done
            
            cd $TMPDIR/dist_staging
            tar -cf $out *
          '';
        };

        packages.omnibus-archive = pkgs.stdenv.mkDerivation {
          pname = "anneal-toolchain-omnibus";
          version = "0.1.0";

          src = pkgs.runCommand "empty-src" {} "mkdir $out";

          nativeBuildInputs = with pkgs; [
            zstd
          ];

          omnibusTar = self.packages.${system}.omnibus-tar;
          ANNEAL_ZSTD_LEVEL = 1;

          buildPhase = ''
            ZSTD_LEVEL=''${ANNEAL_ZSTD_LEVEL:-1}
            echo "Compressing with Zstd level $ZSTD_LEVEL..."
            zstd -$ZSTD_LEVEL $omnibusTar -o $out
          '';

          installPhase = ''
            echo "Archive created at $out"
          '';
        };

        devShells.default = pkgs.mkShell {
          nativeBuildInputs = with pkgs; [
            elan
            graphviz
            python3
            rustup
            zstd
            gnutar
            openssl
            pkg-config
            curl
          ];

          shellHook = ''
            export ANNEAL_AENEAS_TAG="build-2026.04.07.112215-42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4"
            export ANNEAL_RUST_DATE="2026-02-07"
            export ANNEAL_RUST_VERSION="nightly-2026-02-07"
            export LD_LIBRARY_PATH="${pkgs.openssl.out}/lib:$LD_LIBRARY_PATH"
            echo "Welcome to the Anneal hermetic dev shell!"
            echo "Pinned dependencies (elan, graphviz, python3, rustup) successfully configured."
          '';
        };
      });
}
