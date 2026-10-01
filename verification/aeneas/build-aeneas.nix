# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Use the upstream locked compiler/dependencies, changing only the version and
# dropping the post-install Charon symlink. The existing release supplies Charon.
let
  upstream = builtins.getFlake (builtins.getEnv "AENEAS_SOURCE_DIR");
  system = builtins.currentSystem;
  pkgs = import upstream.inputs.nixpkgs { inherit system; };
  base = if pkgs.stdenv.isLinux
    then upstream.packages.${system}.aeneas-static
    else upstream.packages.${system}.aeneas;
  aeneas = base.overrideAttrs (_: {
    AENEAS_VERSION = builtins.getEnv "AENEAS_VERSION";
    postInstall = "";
  });
in pkgs.runCommand "aeneas-nominal-bundle" {
  nativeBuildInputs = pkgs.lib.optionals pkgs.stdenv.isDarwin
    [ pkgs.macdylibbundler ];
} ''
  mkdir -p $out
  cp ${aeneas}/bin/aeneas $out/aeneas
  ${pkgs.lib.optionalString pkgs.stdenv.isDarwin ''
    chmod +w $out/aeneas
    dylibbundler -od -b -x $out/aeneas -d $out/libs -p @executable_path/libs
  ''}
''
