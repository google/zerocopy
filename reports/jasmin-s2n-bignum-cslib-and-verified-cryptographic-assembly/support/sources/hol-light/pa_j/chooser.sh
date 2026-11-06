#!/bin/bash

# Choose an appropriate camlp4 or camlp5 syntax extension.
#
# For OCaml < 3.10 (OCAML_BINARY_VERSION = "3.0"), this uses the built-in
# camlp4, and in general there are different versions for each OCaml version
#
# For OCaml >= 3.10 (OCAML_BINARY_VERSION = "3.1" or "4.x"), this uses the
# separate program camlp5. Now the appropriate syntax extensions is determined
# based on the camlp5 version. The main distinction is < 6.00 and >= 6.00, but
# there are some other incompatibilities, unfortunately.

OCAML_VERSION=`ocamlc -version | cut -c1-4`
OCAML_BINARY_VERSION=`ocamlc -version | cut -c1-3`
OCAML_UNARY_VERSION=`ocamlc -version | cut -c1`
CAMLP5_BINARY_VERSION=`camlp5 -v 2>&1 | cut -f3 -d' ' | cut -c1-4`
CAMLP5_UNARY_VERSION=`camlp5 -v 2>&1 | cut -f3 -d' ' | cut -c1`
CAMLP5_VERSION=`camlp5 -v 2>&1 | cut -f3 -d' ' | cut -f1-3 -d'.' | cut -f1 -d'-' | cut -c1-6`
CAMLP5_FULL_VERSION=`camlp5 -v 2>&1 | cut -f3 -d' ' | cut -f1-3 -d'.' | cut -f1 -d'-' | cut -c1-`

if test ${OCAML_BINARY_VERSION} = "3.0"
then echo "pa_j_${OCAML_VERSION}.ml"
elif test ${CAMLP5_BINARY_VERSION} = "8.04" -o ${CAMLP5_BINARY_VERSION} = "8.05"
then
  if test ${OCAML_BINARY_VERSION} = "5.4"
  then echo "pa_j_5.4_8.04.00.ml"
  else echo "UNKNOWN"
  fi
elif test ${CAMLP5_FULL_VERSION} = "8.03.06"
then echo "pa_j_4.xx_8.03.06.ml"
elif test ${CAMLP5_BINARY_VERSION} = "8.00" -o ${CAMLP5_BINARY_VERSION} = "8.02" \
          -o ${CAMLP5_BINARY_VERSION} = "8.03"
then echo "pa_j_4.xx_${CAMLP5_BINARY_VERSION}.ml"

elif test ${CAMLP5_UNARY_VERSION} = "7"
then
  if test ${CAMLP5_VERSION} = "7.01" -o ${CAMLP5_VERSION} = "7.02" \
          -o ${CAMLP5_VERSION} = "7.03" -o ${CAMLP5_VERSION} = "7.04" \
          -o ${CAMLP5_VERSION} = "7.05" -o ${CAMLP5_VERSION} = "7.06"
  then echo "pa_j_4.xx_7.06.ml"
  else echo "pa_j_4.xx_7.xx.ml"
  fi
elif test ${CAMLP5_VERSION} = "6.02.1"
then echo "pa_j_3.1x_6.02.1.ml"
elif test ${CAMLP5_VERSION} = "6.02.2" -o ${CAMLP5_VERSION} = "6.02.3" \
          -o ${CAMLP5_VERSION} = "6.03" -o ${CAMLP5_VERSION} = "6.04" \
          -o ${CAMLP5_VERSION} = "6.05" -o ${CAMLP5_VERSION} = "6.06"
then echo "pa_j_3.1x_6.02.2.ml"
elif test ${CAMLP5_VERSION} = "6.06" -o ${CAMLP5_VERSION} = "6.07" \
          -o ${CAMLP5_VERSION} = "6.08" -o ${CAMLP5_VERSION} = "6.09" \
          -o ${CAMLP5_VERSION} = "6.10" -o ${CAMLP5_VERSION} = "6.11" \
          -o ${CAMLP5_VERSION} = "6.12" -o ${CAMLP5_VERSION} = "6.13" \
          -o ${CAMLP5_VERSION} = "6.14" -o ${CAMLP5_VERSION} = "6.15" \
          -o ${CAMLP5_VERSION} = "6.16" -o ${CAMLP5_VERSION} = "6.17" ; \
then echo "pa_j_3.1x_6.11.ml"
else echo "pa_j_3.1x_${CAMLP5_UNARY_VERSION}.xx.ml"
fi
