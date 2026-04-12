let
  pkgs = import <nixpkgs> {};
in
pkgs.mkShell rec {
  name = "rustc";
  buildInputs = with pkgs; [
    rustup
    pkg-config
    alsaLib
    libGL
    xorg.libX11
    xorg.libXi
    python39
  ];
  RUST_SRC_PATH = "${pkgs.rust.packages.stable.rustPlatform.rustLibSrc}";
  LD_LIBRARY_PATH = "${pkgs.lib.makeLibraryPath buildInputs}";
}

