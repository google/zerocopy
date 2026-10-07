# Temporary native Intel Mac fixture, using the repaired release's exact tools.
{ flake }:
let
  system = "x86_64-darwin";
  release = flake.packages.${system}.aeneas-download.upstreamRelease;
  pkgs = import flake.inputs.aeneas.inputs.nixpkgs { inherit system; };
  has = name: inputs: builtins.any (input: (input.pname or "") == name) inputs;
in
assert release.system == system;
assert has "sigtool" (release.nativeBuildInputs or []);
assert has "macdylibbundler" (release.buildInputs or []);
assert has "gmp-with-cxx" (pkgs.coreutils.buildInputs or []);
release.overrideAttrs (_: {
  name = "anneal-intel-signing-preflight";
  # Replace the command, eliminating Aeneas/Charon dependencies. Keep inherited
  # stdenv, nativeBuildInputs, buildInputs and the patched bundler unchanged.
  buildCommand = ''
    mkdir "$out"
    cd "$out"
    cp ${pkgs.coreutils}/bin/factor ./factor
    chmod +w ./factor
    dylibbundler -od -b -x ./factor -d ./libs -p @executable_path/libs
    test -x ./factor
    test -d ./libs
  '';
})
