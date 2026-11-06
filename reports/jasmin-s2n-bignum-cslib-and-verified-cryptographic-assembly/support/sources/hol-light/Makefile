###############################################################################
# Makefile for HOL Light                                                      #
#                                                                             #
# Simple "make" just builds the camlp4/camlp5 syntax extension "pa_j.cmo",    #
# which is necessary to load the HOL Light core into the OCaml toplevel.      #
#                                                                             #
# See the README file for more detailed information about the build process.  #
#                                                                             #
# Thanks to Carl Witty for 3.07 and 3.08 ports of pa_j.ml and this process.   #
###############################################################################

# Installation directory for standalone binaries. Set here to the user's
# binary directory. You may want to change it to something like /usr/local/bin

BINDIR=${HOME}/bin

# This is the list of source files in the HOL Light core

HOLSRC=system.ml lib.ml fusion.ml basics.ml nets.ml preterm.ml          \
       parser.ml printer.ml equal.ml bool.ml drule.ml tactics.ml        \
       itab.ml simp.ml theorems.ml ind_defs.ml class.ml trivia.ml       \
       canon.ml meson.ml firstorder.ml metis.ml thecops.ml quot.ml      \
       impconv.ml recursion.ml pair.ml compute.ml                       \
       nums.ml arith.ml wf.ml calc_num.ml normalizer.ml grobner.ml      \
       ind_types.ml lists.ml realax.ml calc_int.ml realarith.ml         \
       real.ml calc_rat.ml int.ml sets.ml iterate.ml cart.ml define.ml  \
       help.ml database.ml update_database.ml hol_lib.ml hol_loader.ml

# Some parameters to help decide how to build things

OCAML_VERSION=`ocamlc -version | cut -c1-4`
OCAML_BINARY_VERSION=`ocamlc -version | cut -c1-3`
OCAML_UNARY_VERSION=`ocamlc -version | cut -c1`

# If set to 1, build hol_lib.cmo and make hol.sh to use it.
# NOTE: This extends the trusted base of HOL Light to include the inliner
# script, inline_load.ml. inline_load.ml is an OCaml program that receives
# an HOL Light proof and replaces the loads/loadt/needs function invocations
# with their actual contents. Please turn this flag on only if having this
# additional trusted base is considered okay.

HOLLIGHT_USE_MODULE?=0

# Main target

default: update_database.ml pa_j.cmo hol.sh;

# Create a local OPAM switch and install dependencies on it.
# This will use the latest OCaml version that fully supports features of
# HOL Light.
# ledit is installed for line editing of OCaml REPL
# Use --no-install to avoid installing HOL Light through the opam file
# in this directory.
switch:; \
  opam update ; \
  opam switch create . ocaml-base-compiler.4.14.0 --no-install ; \
  eval $(opam env) ; \
  opam install -y zarith ledit ; \
  opam pin -y add camlp5 8.03.06

switch-5:; \
  opam update ; \
  opam switch create . ocaml-base-compiler.5.4.0 --no-install ; \
  eval $(opam env) ; \
  opam install -y zarith ledit ; \
  opam pin -y add camlp5 8.04.00

# Choose an appropriate "update_database.ml" file

update_database.ml:; \
  cp update_database/`update_database/chooser.sh` update_database.ml

# Build the camlp4 syntax extension file (camlp5 for OCaml >= 3.10)

pa_j.cmo: pa_j.ml; if test ${OCAML_BINARY_VERSION} = "3.0" ; \
                   then ocamlc -c -pp "camlp4r pa_extend.cmo q_MLast.cmo" -I `camlp4 -where` pa_j.ml ; \
                   elif test ${OCAML_BINARY_VERSION} = "3.1" -o ${OCAML_VERSION} = "4.00" -o ${OCAML_VERSION} = "4.01"  -o ${OCAML_VERSION} = "4.02" -o ${OCAML_VERSION} = "4.03" -o ${OCAML_VERSION} = "4.04" -o ${OCAML_VERSION} = "4.05" ; \
                   then ocamlc -c -pp "camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo" -I `camlp5 -where` pa_j.ml ; \
                   else ocamlc -safe-string -c -pp "camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo" -I `camlp5 -where` -I `ocamlfind query camlp-streams` pa_j.ml ; \
                   fi

pa_j.ml: pa_j/pa_j_3.07.ml pa_j/pa_j_3.08.ml pa_j/pa_j_3.09.ml \
         pa_j/pa_j_3.1x_5.xx.ml pa_j/pa_j_3.1x_6.xx.ml \
         pa_j/pa_j_4.xx_8.00.ml pa_j/pa_j_4.xx_8.02.ml \
         pa_j/pa_j_4.xx_8.03.ml pa_j/pa_j_4.xx_8.03.06.ml \
         pa_j/pa_j_5.4_8.04.00.ml ; \
  cp pa_j/`pa_j/chooser.sh` pa_j.ml

# Choose an appropriate bignum library.

bignum.cmo: bignum_zarith.ml bignum_num.ml ; \
        if test ${OCAML_VERSION} = "4.14" -o ${OCAML_UNARY_VERSION} = "5" ; \
        then ocamlfind ocamlc -package zarith -c -o bignum.cmo bignum_zarith.ml ; \
        else ocamlc -c -o bignum.cmo bignum_num.ml ; \
        fi

bignum.cmx: bignum_zarith.ml bignum_num.ml ; \
        if test ${OCAML_VERSION} = "4.14" -o ${OCAML_UNARY_VERSION} = "5" ; \
        then ocamlfind ocamlopt -package zarith -c -o bignum.cmx bignum_zarith.ml ; \
        else ocamlopt -c -o bignum.cmx bignum_num.ml ; \
        fi

hol_loader.cmo: hol_loader.ml ; \
        ocamlc -verbose -c hol_loader.ml -o hol_loader.cmo

hol_loader.cmx: hol_loader.ml ; \
        ocamlopt -verbose -c hol_loader.ml -o hol_loader.cmx

hol_lib_inlined.ml: ${HOLSRC} inline_load.ml ; \
        HOLLIGHT_DIR="`pwd`" ocaml inline_load.ml hol_lib.ml hol_lib_inlined.ml -omit-prelude

hol_lib.cmo: pa_j.cmo hol_lib_inlined.ml hol_loader.cmo bignum.cmo ; \
        ocamlc -verbose -c -pp "camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo -I . pa_j.cmo" hol_loader.cmo hol_lib_inlined.ml bignum.cmo -o hol_lib.cmo

hol_lib.cma: hol_lib.cmo bignum.cmo hol_loader.cmo ; \
        ocamlfind ocamlc -package zarith -linkpkg -a -o hol_lib.cma bignum.cmo hol_loader.cmo hol_lib.cmo

hol_lib.cmx: pa_j.cmo hol_lib_inlined.ml hol_loader.cmx bignum.cmx ; \
        OCAMLRUNPARAM=l=1000000000 ocamlopt.byte -verbose -c \
              -pp "camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo -I . pa_j.cmo" \
              hol_lib_inlined.ml hol_loader.cmx bignum.cmx -o hol_lib.cmx

hol_lib.cmxa: hol_lib.cmx hol_loader.cmx bignum.cmx ; \
        ocamlfind ocamlopt -package zarith -a -o hol_lib.cmxa bignum.cmx hol_loader.cmx hol_lib.cmx

# Create a bash script 'hol.sh' that loads 'hol.ml' in OCaml REPL.

hol.sh: pa_j.cmo ${HOLSRC} bignum.cmo hol_loader.cmo update_database.ml
	if [ `uname` = "Linux" ] || [ `uname` = "Darwin" ] ; then \
		if [ ${OCAML_UNARY_VERSION} = "5" ] || [ ${OCAML_VERSION} = "4.14" ] ; then \
			ocamlfind ocamlmktop -package zarith -o ocaml-hol zarith.cma bignum.cmo hol_loader.cmo ; \
			sed "s^__DIR__^`pwd`^g; s^__USE_MODULE__^$(HOLLIGHT_USE_MODULE)^g" hol_4.14.sh > hol.sh ; \
		else \
			ocamlmktop -o ocaml-hol nums.cma bignum.cmo hol_loader.cmo ; \
			sed "s^__DIR__^`pwd`^g; s^__USE_MODULE__^$(HOLLIGHT_USE_MODULE)^g" hol_4.sh > hol.sh ; \
		fi ; \
		chmod +x hol.sh ; \
	else \
		echo 'FAILURE: hol.sh assumes Linux' ; \
	fi

# If HOLLIGHT_USE_MODULE is set, add hol_lib.cmo to dependency of hol.sh
# Also, build the test suites in UnitTests/ using both OCaml bytecode compiler
# and OCaml native compiler. Native builds go via `hol.sh compile/link`;
# bytecode builds invoke ocamlfind directly because hol.sh has no byte mode.

ifeq ($(HOLLIGHT_USE_MODULE),1)
hol.sh: hol_lib.cmo

# UnitTests/basic_tests.ml: general HOL Light correctness checks.
UnitTests/basic_tests_inlined.ml: UnitTests/basic_tests.ml inline_load.ml hol.sh ; \
        ./hol.sh inline-load UnitTests/basic_tests.ml UnitTests/basic_tests_inlined.ml
UnitTests/basic_tests.byte: UnitTests/basic_tests_inlined.ml hol_lib.cmo hol.sh ; \
        ocamlfind ocamlc -package zarith -linkpkg -pp "`./hol.sh -pp`" \
        -I . bignum.cmo hol_loader.cmo hol_lib.cmo \
        UnitTests/basic_tests_inlined.ml -o UnitTests/basic_tests.byte
UnitTests/basic_tests.native: UnitTests/basic_tests_inlined.cmx hol_lib.cmxa hol.sh ; \
        ./hol.sh link UnitTests/basic_tests_inlined.cmx -o UnitTests/basic_tests.native
UnitTests/basic_tests_inlined.cmx: UnitTests/basic_tests_inlined.ml hol_lib.cmxa hol.sh ; \
        ./hol.sh compile UnitTests/basic_tests_inlined.ml

# UnitTests/printer_tests.ml: pp_print_term output verification.
UnitTests/printer_tests_inlined.ml: UnitTests/printer_tests.ml inline_load.ml hol.sh ; \
        ./hol.sh inline-load UnitTests/printer_tests.ml UnitTests/printer_tests_inlined.ml
UnitTests/printer_tests.byte: UnitTests/printer_tests_inlined.ml hol_lib.cmo hol.sh ; \
        ocamlfind ocamlc -package zarith -linkpkg -pp "`./hol.sh -pp`" \
        -I . bignum.cmo hol_loader.cmo hol_lib.cmo \
        UnitTests/printer_tests_inlined.ml -o UnitTests/printer_tests.byte
UnitTests/printer_tests.native: UnitTests/printer_tests_inlined.cmx hol_lib.cmxa hol.sh ; \
        ./hol.sh link UnitTests/printer_tests_inlined.cmx -o UnitTests/printer_tests.native
UnitTests/printer_tests_inlined.cmx: UnitTests/printer_tests_inlined.ml hol_lib.cmxa hol.sh ; \
        ./hol.sh compile UnitTests/printer_tests_inlined.ml

default: hol_lib.cma hol_lib.cmxa \
         UnitTests/basic_tests.byte UnitTests/basic_tests.native \
         UnitTests/printer_tests.byte UnitTests/printer_tests.native
endif

# Build a standalone hol image called "hol" (needs Linux and DMTCP)

hol: hol.sh make-checkpoint.sh update_database.ml;                      \
     if test `uname` = Linux; then                                      \
     ./make-checkpoint.sh hol "loadt \"update_database.ml\"" ;          \
     else                                                               \
     echo '******************************************************';     \
     echo 'FAILURE: Image build assumes Linux and DMTCP';               \
     echo '******************************************************';     \
     fi

# Build an image with multivariate calculus preloaded.

hol.multivariate: hol.sh make-checkpoint.sh Multivariate/make.ml        \
     Library/card.ml Library/permutations.ml Library/products.ml        \
     Library/floor.ml Multivariate/misc.ml Library/iter.ml              \
     Multivariate/metric.ml Multivariate/vectors.ml                     \
     Multivariate/determinants.ml Multivariate/topology.ml              \
     Multivariate/convex.ml Multivariate/paths.ml                       \
     Multivariate/polytope.ml Multivariate/degree.ml                    \
     Multivariate/derivatives.ml Multivariate/clifford.ml               \
     Multivariate/integration.ml Multivariate/measure.ml                \
     Multivariate/multivariate_database.ml update_database.ml;          \
     if test `uname` = Linux; then                                      \
     ./make-checkpoint.sh hol.multivariate "loadt \"Multivariate/make.ml\"; loadt \"update_database.ml\""; \
     else                                                               \
     echo '******************************************************';     \
     echo 'FAILURE: Image build assumes Linux and DMTCP';               \
     echo '******************************************************';     \
     fi

# Build an image with analysis and SOS procedure preloaded

hol.sosa: hol.sh make-checkpoint.sh                                     \
     Library/analysis.ml Library/transc.ml                              \
     Examples/sos.ml update_database.ml;                                \
     if test `uname` = Linux; then                                      \
     ./make-checkpoint.sh hol.sosa "loadt \"Library/analysis.ml\"; loadt \"Library/transc.ml\"; loadt \"Examples/sos.ml\"; loadt \"update_database.ml\""; \
     else                                                               \
     echo '******************************************************';     \
     echo 'FAILURE: Image build assumes Linux and DMTCP';               \
     echo '******************************************************';     \
     fi

# Build an image with cardinal arithmetic preloaded

hol.card: hol.sh make-checkpoint.sh Library/card.ml update_database.ml; \
     if test `uname` = Linux; then                                      \
     ./make-checkpoint.sh hol.card "loadt \"Library/card.ml\"; loadt \"update_database.ml\""; \
     else                                                               \
     echo '******************************************************';     \
     echo 'FAILURE: Image build assumes Linux and DMTCP';               \
     echo '******************************************************';     \
     fi

# Build an image with multivariate-based complex analysis preloaded

hol.complex: hol.sh make-checkpoint.sh                                  \
     Multivariate/make.ml                                            \
     Library/card.ml Library/permutations.ml Library/products.ml     \
     Library/floor.ml Multivariate/misc.ml Library/iter.ml           \
     Multivariate/metric.ml Multivariate/vectors.ml                  \
     Multivariate/determinants.ml Multivariate/topology.ml           \
     Multivariate/convex.ml Multivariate/paths.ml                    \
     Multivariate/polytope.ml Multivariate/degree.ml                 \
     Multivariate/derivatives.ml Multivariate/clifford.ml            \
     Multivariate/integration.ml Multivariate/measure.ml             \
     Multivariate/multivariate_database.ml                           \
     Library/binomial.ml Multivariate/complexes.ml                   \
     Multivariate/canal.ml Multivariate/transcendentals.ml           \
     Multivariate/realanalysis.ml Multivariate/moretop.ml            \
     Multivariate/cauchy.ml Multivariate/complex_database.ml         \
     update_database.ml;                                             \
     if test `uname` = Linux; then                                   \
     ./make-checkpoint.sh hol.complex "loadt \"Multivariate/make.ml\"; loadt \"update_database.ml\"; loadt \"Multivariate/complexes.ml\"; loadt \"Multivariate/canal.ml\"; loadt \"Multivariate/transcendentals.ml\"; loadt \"Multivariate/realanalysis.ml\"; loadt \"Multivariate/cauchy.ml\"; loadt \"Multivariate/complex_database.ml\"; loadt \"update_database.ml\""; \
     else                                                           \
     echo '******************************************************'; \
     echo 'FAILURE: Image build assumes Linux and DMTCP';           \
     echo '******************************************************'; \
     fi

# Build all those
all: hol.sh hol hol.multivariate hol.sosa hol.card hol.complex;

# Build binaries and copy them to binary directory

install: hol.sh hol hol.multivariate hol.sosa hol.card hol.complex; cp hol hol.multivariate hol.sosa hol.card hol.complex ${BINDIR}

# Clean up all compiled files

clean:; \
  rm -rf bignum.c* bignum.o \
         update_database.ml pa_j.ml pa_j.cmi pa_j.cmo \
         hol_lib.a hol_lib.c* hol_lib.o hol_lib_inlined.ml \
         hol_loader.c* hol_loader.o \
         UnitTests/basic_tests_inlined.* \
         UnitTests/basic_tests.byte UnitTests/basic_tests.native \
         UnitTests/printer_tests_inlined.* \
         UnitTests/printer_tests.byte UnitTests/printer_tests.native \
         ocaml-hol hol.sh hol hol.ckpt \
         hol.multivariate hol.multivariate.ckpt \
         hol.sosa hol.sosa.ckpt \
         hol.card hol.card.ckpt \
         hol.complex hol.complex.ckpt
