<!--
     Copyright 2018, Data61, CSIRO
     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Manifest repository

This repository contains google [repo] manifest files for the verification
repository collection. It manages the collection of repositories that are needed
for the verification of the seL4 microkernel. In particular, these repositories
include the proofs, the kernel sources, the theorem prover Isabelle/HOL, the
theorem prover HOL4, and the binary verification tool chain.

[repo]: https://gerrit.googlesource.com/git-repo/+/HEAD/README.md

## Contents

The manifest files stored here come in three categories:

- `default.xml`: this manifest stores the latest tested-as-working combination
  of the seL4 code and proof repositories. It is updated automatically by CI jobs.
  It points to specific revision hashes, and should generally not be modified manually.

- `mcs.xml`: this manifest stores the latest tested-as-working combination of
  the seL4 code and proof repositories for the MCS proofs (the `rt` branch in
  the `l4v` repository). It is updated automatically by CI jobs. It points to
  specific revision hashes, and should generally not be modified manually.

- development manifests such as `devel.xml` and `mcs-devel.xml`: these are for
  proof development and typically point to branch names of the verification
  repositories in combination with a fixed revision hash of the seL4 code
  repository. The seL4 revision in `devel.xml` and `mcs-devel.xml` is updated
  automatically by CI jobs for code changes in seL4 that are not visible to the
  proofs. It should be updated manually or using the [version bump][] script
  whenever proofs are updated in sync with the code. This will then trigger a CI
  run and, if successful, a corresponding update in `default.xml` or `mcs.xml`.

- release version manifests such as `12.0.0.xml`: these store the repository
  version configuration for official releases of seL4. Use these to check proofs
  for release versions.

[version bump]: https://github.com/seL4/l4v/tree/master/misc/bump

## Use

To build the seL4 proofs, please follow the [setup] instructions in the [l4v]
repository.

For build instructions for the binary verification, see the [graph-refine]
repository.

[setup]: https://github.com/seL4/l4v/blob/master/docs/setup.md
[l4v]: https://github.com/seL4/l4v/
[graph-refine]: (https://github.com/seL4/graph-refine/)
