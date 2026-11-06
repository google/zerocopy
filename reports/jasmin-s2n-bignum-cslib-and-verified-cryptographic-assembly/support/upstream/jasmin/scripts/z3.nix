{ z3, fetchFromGitHub }:

z3.overrideAttrs (_: rec {
  version = "4.16.0";
  src = fetchFromGitHub {
    owner = "Z3Prover";
    repo = "z3";
    tag = "z3-${version}";
    hash = "sha256-DnhX3kxggnFmyYwXEPBsBA1rh4oor1oIJR5TMJk/jvc=";
  };
})
