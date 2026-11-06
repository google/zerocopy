{ super, lib, fetchFromGitHub, }:

let rev = "86ed49aeca65a8d32e81bb386778f49b45ee505b"; in

super.mathcomp-word.overrideAttrs (o: {
  name = "${(lib.parseDrvName o.name).name}-3.5-git-${builtins.substring 0 8 rev}";
  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "coqword";
    inherit rev;
    hash = "sha256-TdjMp/4Eo9uEcUWhV3OSy/eX1GzQO2nhym3MNTzNvwY=";
  };
})
