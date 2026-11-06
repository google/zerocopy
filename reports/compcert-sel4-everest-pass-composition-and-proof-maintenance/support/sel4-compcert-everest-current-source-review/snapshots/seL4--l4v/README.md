<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

[![DOI][0]](http://dx.doi.org/10.5281/zenodo.591732)
[![CI](https://github.com/seL4/l4v/actions/workflows/push.yml/badge.svg)](https://github.com/seL4/l4v/actions/workflows/push.yml)
[![Proofs](https://github.com/seL4/l4v/actions/workflows/proof-deploy.yml/badge.svg?branch=master)](https://github.com/seL4/l4v/actions/workflows/proof-deploy.yml?query=branch%3Amaster)
[![Weekly Clean](https://github.com/seL4/l4v/actions/workflows/weekly-clean.yml/badge.svg)](https://github.com/seL4/l4v/actions/workflows/weekly-clean.yml)
[![External](https://github.com/seL4/l4v/actions/workflows/external.yml/badge.svg)](https://github.com/seL4/l4v/actions/workflows/external.yml)

MCS:\
[![CI](https://github.com/seL4/l4v/actions/workflows/push.yml/badge.svg?branch=rt)](https://github.com/seL4/l4v/actions/workflows/push.yml)
[![MCS Proofs](https://github.com/seL4/l4v/actions/workflows/proof-deploy.yml/badge.svg?branch=rt)](https://github.com/seL4/l4v/actions/workflows/proof-deploy.yml?query=branch%3Art)

  [0]: https://zenodo.org/badge/doi/10.5281/zenodo.591732.svg


[The L4.verified Proofs][1]
===========================

This is the L4.verified git repository with formal specifications and
proofs for the seL4 microkernel.

Most proofs in this repository are conducted in the interactive proof
assistant [Isabelle/HOL][2]. For an introduction to Isabelle, see its
[official website][2] and [documentation][3].

  [1]: https://github.com/seL4/l4v                   "L4.verified Repository"
  [2]: https://isabelle.in.tum.de                    "Isabelle Website"
  [3]: https://isabelle.in.tum.de/documentation.html "Isabelle Documentation"

<a name="setup"></a>
Setup
-----

This repository is meant to be used as part of a Google [repo][5] setup. Instead
of cloning it directly, please follow the directions for software dependencies
and Isabelle installation in the [setup.md](docs/setup.md) file in the `docs`
directory.

[5]: https://gerrit.googlesource.com/git-repo/+/HEAD/README.md

Contributing
------------

Contributions to this repository are welcome.
Please read [`CONTRIBUTING.md`](CONTRIBUTING.md) for details.

Overview
--------

The repository is organised as follows.

 * [`docs`](docs/): documentation on conventions, style, etc.

 * [`spec`](spec/): a number of different formal specifications of seL4
    * [`abstract`](spec/abstract/): the functional abstract specification of seL4
    * [`sep-abstract`](spec/sep-abstract/): an abstract specification for a reduced
      version of seL4 that is configured as a separation kernel
    * [`haskell`](spec/haskell/): Haskell model of the seL4 kernel, kept in sync
      with the C code
    * [`machine`](spec/machine/): the machine interface of these two specifications
    * [`cspec`](spec/cspec/): the entry point for automatically translating the seL4 C code
      into Isabelle
    * [`capDL`](spec/capDL/): a specification of seL4 that abstracts from memory content and
      concrete execution behaviour, modelling the protection state of the
      system in terms of capabilities. This specification corresponds to the
      capability distribution language *capDL* that can be used to initialise
      user-level systems on top of seL4.
    * [`take-grant`](spec/take-grant/): a formalisation of the classical take-grant security
    model, applied to seL4, but not connected to the code of seL4.

    * There are additional specifications that are not tracked in this repository,
      but are generated from other files:
      * [`design`](spec/design/): the design-level specification of seL4,
        generated from the Haskell model.
      * [`c`](spec/cspec/c/): the C code of the seL4 kernel, preprocessed into a form that
        can be read into Isabelle. This is generated from the [seL4 repository](https://github.com/seL4/seL4).

 * [`proof`](proof/): the seL4 proofs
    * [`invariant-abstract`](proof/invariant-abstract/): invariants of the seL4 abstract specification
    * [`refine`](proof/refine/): refinement between abstract and design specifications
    * [`crefine`](proof/crefine/): refinement between design specification and C semantics
    * [`access-control`](proof/access-control/): integrity and authority confinement proofs
    * [`infoflow`](proof/infoflow/): confidentiality and intransitive non-interference proofs
    * [`asmrefine`](proof/asmrefine/): Isabelle/HOL part of the seL4 binary verification
    * [`drefine`](proof/drefine/): refinement between capDL and abstract specification
    * [`sep-capDL`](proof/sep-capDL/): a separation logic instance on capDL
    * [`capDL-api`](proof/capDL-api/): separation logic specifications of selected seL4 APIs

 * [`lib`](lib/): generic proof libraries, proof methods and tools. Among these,
   further libraries for fixed-size machine words, a formalisation of state
   monads with nondeterminism and exceptions, a generic verification condition
   generator for monads, a recursive invariant prover for these (`crunch`), an
   abstract separation logic formalisation, a prototype of the [Eisbach][6] proof
   method language, a prototype `levity` refactoring tool, and others.

 * [`tools`](tools/): larger, self-contained proof tools
    * [`asmrefine`](tools/asmrefine/): the generic Isabelle/HOL part of the binary
      verification tool
    * [`c-parser`](tools/c-parser/): a parser from C into the Simpl language in Isabelle/HOL.
       Includes a C memory model.
    * [`autocorres`](tools/autocorres/): an automated, proof-producing abstraction tool from
      C into higher-level Isabelle/HOL functions, based on the C parser above
    * [`haskell-translator`](tools/haskell-translator/): a basic python script for converting the Haskell
      prototype of seL4 into the executable design specification in
      Isabelle/HOL.

 * [`misc`](misc/): miscellaneous scripts and build tools

 * [`camkes`](camkes/): an initial formalisation of the CAmkES component platform
    on seL4. Work in progress.

 * [`sys-init`](sys-init/): specification of a capDL-based, user-level system initialiser
    for seL4, with proof that the specification leads to correctly initialised
    systems.


  [6]: https://trustworthy.systems/publications/nictaabstracts/Matichuk_WM_14.abstract "An Isabelle Proof Method Language"


Hardware requirements
---------------------

Almost all proofs in this repository should work within 4GB of RAM. Proofs
involving the C refinement, will usually need the 64bit mode of polyml and
about 16GB of RAM.

The proofs distribute reasonably well over multiple cores, up to about 8
cores are useful.

Running the Proofs
------------------

If Isabelle is set up correctly, a full test for the proofs in this repository
for seL4 on the `ARM` architecture can be run with the command

    L4V_ARCH=ARM ./run_tests

from the directory `l4v/`.

Set the environment variable `L4V_ARCH` to one of `ARM`, `ARM_HYP`, `X64`,
`RISCV64`, or `AARCH64` to get the proofs for the respective architecture. `ARM`
has the most complete set of proofs, the other architectures tend to support
only a subset of the proof sessions defined for `ARM`.

Not all of the proof sessions can be built directly with the `isabelle build`
command. The seL4 proofs depend on Isabelle specifications that are generated
from the C source code and Haskell model. Therefore, it is recommended to always
build using the `run_tests` command or the supplied Makefiles, which will ensure
that these generated specs are up to date.

To do this, enter one level under the `l4v/` directory and run `make <session-name>`.
For example, to build the abstract specification, do

    export L4V_ARCH=ARM
    cd l4v/spec
    make ASpec

See the `HEAPS` variable in the corresponding `Makefile` for available targets.
The sessions that directly depend on generated sources are `ASpec`, `ExecSpec`,
and `CKernel`. These, and all sessions that depend on them, need to be run using
`run_tests` or `make`.

Proof sessions that do not depend on generated inputs can be built directly with

    ./isabelle/bin/isabelle build -d . -v -b <session name>

from the directory `l4v/`. For available sessions and their dependencies, see
the corresponding `ROOT` files in this repository. There is roughly one session
corresponding to each major directory in the repository.

For interactively exploring, say the invariant proof of the abstract
specification on `ARM`, note that in `proof/ROOT` the parent session for
`AInvs` is `ASpec` and therefore run:

    export L4V_ARCH=ARM
    ./run_tests ASpec
    ./isabelle/bin/isabelle jedit -d . -R AInvs

or, if you prefer `make`:

    export L4V_ARCH=ARM
    cd spec; make ASpec
    ../isabelle/bin/isabelle jedit -d . -R AInvs

in `l4v/` and open one of the files in `proof/invariant-abstract`.
