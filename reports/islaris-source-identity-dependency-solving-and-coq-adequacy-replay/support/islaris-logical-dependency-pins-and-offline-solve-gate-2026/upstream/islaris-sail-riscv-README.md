# Linking Islaris proofs to the Sail generated Coq model

This directory contains some infrastructure to connect Islaris to the
Coq model generated from the RISC-V Sail model.

## Installation
The Coq code generated from the sail model needs to be installed
separately. This can be done by calling `make saildep` in the root
directory of this repository. This command installs the Coq code
generated from the RISC-V Sail model into the current opam switch.

Note that this command requires `z3` to be installed. One can install it with
`opam install z3`.

Afterwards one has to enable compilation of this directory by running
`make enable-sail-riscv` in the root directory of this repository.
Afterwards, the files in this folder are compiled together with the
rest of the repository when running `make`.
