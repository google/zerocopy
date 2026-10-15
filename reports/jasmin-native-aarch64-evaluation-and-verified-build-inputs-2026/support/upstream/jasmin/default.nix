{ pkgs ? import (if pinned-nixpkgs then scripts/nixpkgs.nix else <nixpkgs>) {}
, inCI ? false
, pinned-nixpkgs ? inCI
, coqDeps ? !inCI
, coqMaster ? false
, ocamlDeps ? !inCI
, pyDeps ? testDeps
, runDeps ? testDeps
, safetyDeps ? !inCI
, testDeps ? !inCI
, devTools ? !inCI
, ecRef ? ""
, opamDeps ? false
, enableFramePointers ? false
}:

with pkgs;

let inherit (lib) optionals; in

let coqPackages =
  if coqMaster then
    let elpi-version = "3.8.0"; in
    let rocqPackages = pkgs.rocqPackages.overrideScope (self: super: {
      rocq-core = super.rocq-core.override { version = "master"; };
      rocq-elpi = super.rocq-elpi.override { version = "master"; inherit elpi-version; };
      micromega-plugin = super.micromega-plugin.override { version = "master"; };
      stdlib = super.stdlib.override { version = "master"; };
    });
    in
    pkgs.coqPackages.overrideScope (self: super: {
      coq = super.coq.override { version = "master"; inherit rocqPackages; };
      inherit (rocqPackages) stdlib;
      mathcomp = super.mathcomp.override { version = "master"; };
      mathcomp-word = super.mathcomp-word.override { version = "master"; };
      mathcomp-zify = super.mathcomp-zify.override { version = "master"; };
      coq-elpi = super.coq-elpi.override { version = "master"; inherit elpi-version; };
      hierarchy-builder = super.hierarchy-builder.override { version = "master"; };
      ExtLib = super.ExtLib.override { version = "master"; };
      paco = super.paco.override { version = "master"; };
      ITree = super.ITree.override { version = "master"; };
    })
  else coqPackages_9_0.overrideScope (self: super: {
      coq-elpi = super.coq-elpi.override {
        version = "2.5.2";
        elpi-version = "2.0.7";
      };
      hierarchy-builder = super.hierarchy-builder.override { version = "1.9.1"; };
      mathcomp = super.mathcomp.override { version = "2.4.0"; };
      mathcomp-word = callPackage scripts/mathcomp-word.nix { inherit super; };
    })
; in

let easycrypt = callPackage scripts/easycrypt.nix {
  inherit ecRef;
  why3 = pkgs.why3.override {
    ideSupport = false;
    coqPackages = { coq = null; flocq = null; };
  };
}; in

let z3 = callPackage scripts/z3.nix {}; in

let inherit (coqPackages.coq) ocamlPackages; in

let oP =
  if enableFramePointers
  then ocamlPackages.overrideScope (self: super: {
      ocaml = super.ocaml.override { framePointerSupport = true; };
  })
  else ocamlPackages
; in

if !lib.versionAtLeast oP.ocaml.version "4.11"
then throw "Jasmin requires OCaml ≥ 4.11"
else

let ecDeps = ecRef != ""; in

stdenv.mkDerivation {
  name = "jasmin-0";
  src = nix-gitignore.gitignoreSource [] ./.;
  buildInputs = []
    ++ optionals coqDeps [
      coqPackages.coq
      coqPackages.mathcomp-word
      coqPackages.ITree
    ]
    ++ optionals runDeps [ curl.bin gmp ]
    ++ optionals pyDeps (with python3Packages; [ python pyyaml ])
    ++ optionals testDeps [ llvmPackages.bintools-unwrapped ]
    ++ optionals safetyDeps [ oP.apron.out ]
    ++ optionals ocamlDeps ([ dune ] ++ (with oP; [
         ocaml findlib
         cmdliner
         angstrom
         batteries
         menhir menhirLib zarith yojson ]))
    ++ optionals (ocamlDeps && safetyDeps) [ ppl oP.apron ]
    ++ optionals devTools ([ coqPackages.coq-lsp ] ++ (with oP; [ merlin ocaml-lsp ]))
    ++ optionals ecDeps [ easycrypt z3.out ]
    ++ optionals opamDeps [ rsync git pkg-config perl ppl mpfr opam ]
    ;

  enableParallelBuilding = true;

  installPhase = ''
    make -C compiler install PREFIX=$out
  '';
}
