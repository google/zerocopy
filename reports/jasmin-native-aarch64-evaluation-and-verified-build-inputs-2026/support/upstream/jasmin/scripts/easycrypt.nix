{ ecRef
, lib
, stdenv
, fetchFromGitHub
, fetchpatch
, dune
, ocamlPackages
, python3
, why3
, fetchurl
}:

with {

  "dev" = {
    version = "main";
    rev = "????";
    src = builtins.fetchTarball "https://api.github.com/repos/easycrypt/easycrypt/tarball/main";
    extraBuildInputs = [ ];
  };

  "release" = rec {
    version = "2026.09";
    rev = "r${version}";
    src = fetchFromGitHub {
      owner = "easycrypt";
      repo = "easycrypt";
      inherit rev;
      hash = "sha256-7ZnGZOZyV5znDGzg0c3XSsliQyOFOwJp2iyAzJtDNwk=";
    };
    extraBuildInputs = [];
  };

}."${ecRef}";

stdenv.mkDerivation rec {
  pname = "easycrypt";
  inherit version src;

  nativeBuildInputs = with ocamlPackages; [
    dune
    findlib
    menhir
    ocaml
    python3.pkgs.wrapPython
  ];

  buildInputs = with ocamlPackages; [
    batteries
    bitwuzla-cxx
    dune-build-info
    dune-site
    markdown
    pcre2
    why3
    yojson
    zarith
  ] ++ extraBuildInputs;

  propagatedBuildInputs = [ why3.out ];

  strictDeps = true;

  postPatch = ''
    substituteInPlace dune-project --replace-fail '(name easycrypt)' '(name easycrypt)(version ${rev})'
  '';

  pythonPath = with python3.pkgs; [ pyyaml ];

  installPhase = ''
    runHook preInstall
    dune install --prefix $out ${pname}
    rm -rf $out/lib/easycrypt/ecLib
    rm $out/bin/ec-runtest
    wrapPythonProgramsIn "$out/lib/easycrypt/commands" "$pythonPath"
    runHook postInstall
  '';

}
