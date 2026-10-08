# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Reuse Anneal's configured input graph, including its Charon nixpkgs follows.
let
  anneal = builtins.getFlake (builtins.getEnv "ANNEAL_FLAKE_DIR");
  system = builtins.currentSystem;
  pkgs = import anneal.inputs.nixpkgs { inherit system; };
  upstream = anneal.inputs.aeneas;
  base = if pkgs.stdenv.isLinux
    then upstream.packages.${system}.aeneas-static
    else upstream.packages.${system}.aeneas;
  aeneas = base.overrideAttrs (_: {
    src = builtins.path {
      path = (builtins.getEnv "AENEAS_SOURCE_DIR") + "/src";
      name = "aeneas-patched-src";
    };
    AENEAS_VERSION = builtins.getEnv "AENEAS_VERSION";
    postInstall = "";
  });
  charonBase = upstream.inputs.charon.packages.${system};
  charon = charonBase.charon-unwrapped.overrideAttrs (old: {
    patches = (old.patches or []) ++ [ ./patches/admission-snapshot.patch ];
  });
  portableCharon = charonBase.charon-portable.overrideAttrs (_: {
    unpackPhase = ''
      mkdir bin
      cp ${charon}/bin/charon ${charon}/bin/charon-driver bin/
      chmod -R u+w bin
    '';
  });
in pkgs.runCommand "aeneas-nominal-bundle" {
  nativeBuildInputs = anneal.packages.${system}.aeneas-download.portabilityInputs;
} ''
  mkdir -p $out
  cp ${aeneas}/bin/aeneas $out/aeneas
  cp ${portableCharon}/bin/charon ${portableCharon}/bin/charon-driver $out/
  ${pkgs.lib.optionalString pkgs.stdenv.isDarwin ''
    chmod +w $out/aeneas
    dylibbundler -od -b -x $out/aeneas -d $out/libs -p @executable_path/libs
  ''}
''
