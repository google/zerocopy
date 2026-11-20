Support material for the report in ../REPORT.md.

loc/abella_loc.py
    Classifies non-blank, non-comment lines of Abella .thm files into
    'spec' (Kind/Type/Define/... declarations and theorem statements) and
    'proof' (tactic lines after a theorem statement), and counts Theorem
    commands and 'skip' tactics.
loc/count_loc.py
    Non-blank, non-comment line counts for Coq (.v), Agda (.agda), Beluga
    (.bel) and F* (.fst); for Coq also splits lines inside Proof...Qed/Defined/
    Admitted from lines outside; counts Admitted/admit/postulate/Axiom/assume
    tokens.
loc/typingformalization_abella_loc.txt   abella_loc.py over src/*.thm of
                                          JimmyZJX/TypingFormalization at the pinned revision.
loc/poplmark_reloaded_loc.txt            count_loc.py over the pinned poplmark-reloaded tree.
loc/certint_loc.txt                      count_loc.py over all .v files of garrigue/certint.
loc/miniml_loc.txt                       wc -l / non-blank line counts of the 1998 Isabelle
                                          MiniML theory (.thy definitions, .ML proof scripts)
                                          and of the current AFP Isar version.

abella/inputs.sha256                     SHA-256 of the 15 .thm inputs that were checked.
abella/v2.0.7_full_check_time.txt        GNU time -v summary of a clean batch check of
                                          smallStep.thm (which imports every other file)
                                          with Abella v2.0.7, plus counts of compiled .thc
                                          files, 'Proof completed' messages and errors.
abella/v2.0.8.3_decl_failure_excerpt.txt Tail of decl.out when the same inputs are checked
                                          with Abella v2.0.8.3 (the run stops in decl.thm).

Reproduce the Abella check (Linux, OCaml toolchain with ocamlbuild/ocamlfind):
  1. Fetch abella-prover/abella at tag v2.0.7
     (commit 5f6a6122e990f32a3718e1f7efaf29469fd22606) and build with
     OCAMLPARAM="_,warn-error=-a,w=-a" make all
     (the relaxed warning flags were needed with OCaml 5.4; the build
     otherwise stops on warning 70, missing .mli).
  2. Copy src/*.thm of JimmyZJX/TypingFormalization
     (commit 7f0596031be9ee08b5f7b5a7678a284240e95805) into an empty
     directory, verify against inputs.sha256, and run
     /usr/bin/time -v <abella-v2.0.7>/abella smallStep.thm -o smallStep.out
  3. Expect exit status 0, 14 .thc files and 586 'Proof completed' messages.
