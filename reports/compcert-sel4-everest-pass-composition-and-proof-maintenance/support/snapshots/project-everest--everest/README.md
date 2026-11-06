# Project Everest

Efficient, verified components for the HTTPS ecosystem.

See [the website](https://project-everest.github.io)!

## The `everest` script

The role of this script is to:
- check that your development environment is sane;
- fetch known good revisions of miTLS, F\*, KaRaMeL, Vale and HACL
- run the voodoo series of commands that will lead to a successful build
- run whatever is known to be working tests.

For developers, this script also allows you to:
- record a new known set of good revisions.

This script is used heavily by [continuous
integration](https://github.com/project-everest/everest-ci) to pull, build &
test project everest.

## Pre-setup (Windows)

The script requires Visual Studio (specifically the F# and C++ components) to
be present on your system. If you do not have it, you can install the
[community edition](https://visualstudio.microsoft.com/vs/community/).

If you don't have Opam for Windows installed already, please download and run
the [64-bit installer](https://fdopen.github.io/opam-repository-mingw/installation/).
It will also install Cygwin, then you can launch this script from a Cygwin prompt.

## Usage

See `./everest help`

## Contributing

We welcome pull requests to this script, using the usual fork project + pull
request GitHub model. For members of Everest, Jonathan Protzenko has the keys
to the everest project on GitHub and can grant write permissions on this
repository so that you can develop your feature in a branch directly. To be a member of the Everest team with access to the build system, please contact Jonathan for more info. Jonathan watches pull requests and will provide timely feedback unless he's on vacations
or in another timezone.

# A guided tour of the code

A Docker image is built and uploaded to the Docker Hub after a successful
verification run of all projects. One can fetch it via `docker pull
projecteverest/everest`. If you are running from this image, or if you
have checked out all projects, here are some highlights from Project Everest.

## Finding the proofs

Based our paper [Verified Low-Level Programming Embedded in
F*](https://arxiv.org/abs/1703.00053):
- **Fig. 2, "A snippet from Chacha20"**:
  `hacl-star/code/salsa-family/Hacl.Impl.Chacha20.fst`:777 for the
  implementation, and `hacl-star/code/salsa-family/Chacha20.fsti` for the
  interface
- **2.2, Low\* heap model**:
  + `FStar/ulib/FStar.HyperHeap.fst`, for the definition of `rid`,
    `root`, etc.
  + `FStar/ulib/FStar.HyperStack.fst`, for the definition of
    `is_stack_region`, `sid`, the `mem` type, etc.
  + `FStar/ulib/hyperstack/FStar.ST.fst`, for the definition of
    `push_frame`, the allocation functions, the `Stack` and `StackInline`
    effects, etc.
- **2.2, Modeling arrays:**
  in `FStar/ulib/FStar.Buffer.fst`
- **2.2, Modeling structs:**
  in `FStar/ulib/FStar.Struct.fst`
- **2.2, Modeling structs, in-progress unified model of flat, inline arrays within
  structs:**
  in `FStar/ulib/FStar.StructNG.fst`
- **2.3, abstract limb type:**
  in `hacl-star/code/bignum/Hacl.Bignum.Limb.fst`, including the the definition
  of `v` and `eq_mask`
- **Fig. 3, Poly1305 bigint:**
  + since the paper was written, our Poly1305 version was ported to 64-bits; the
    new normalization functions are in `hacl-star/code/poly1305/Hacl.Bignum.Modulo.fst`, and
    the closest equivalent of `poly1305_mac` is `poly1305_last_pass_` in
    `hacl-star/code/poly1305/Hacl.Impl.Poly1305_64.fst`
  + we also include an older version of our codebase for reference purposes; the
    `normalize` function is in
    `FStar/examples/low-level/crypto/Crypto.Symmetric.Poly1305.Bignum.fst` and
    is called `finalize`; the `poly1305_mac` function is in
    `FStar/examples/low-level/crypto/Crypto.Symmetric.Poly1305.fst`:1083. 
    **Note:** this code no longer verifies, as this directory has been phased
    out in favor of the new, improved proofs in HACL\*
- **2.4, AEAD security proof:**
  the AEAD development has been integrated with the HACL* library; the
  top-level AEAD proof statement, `encrypt`, is in
  `hacl-star/secure-api/aead/Crypto.AEAD.Encrypt.fst`
- **2.4, StackInline**
  see `hacl-star/secure_api/uf1cma/Crypto.Symmetric.MAC.fst`:216, including an
  example of multiplexing, where we deal with different types of MACs depending
  on which algorithm is used. This pattern also extracts to C.


## Source code for our tools

- **4, the KaRaMeL tool:**
  the source of KaRaMeL are included in `karamel`; of notable
  interest are the files
  `karamel/src/Simplify.ml` (many rewriting passes),
  `karamel/src/Inlining.ml` (inlining of the `StackInline` effect),
  `karamel/src/DataTypes.ml` (compilation of data types and pattern
  matches),
  `karamel/src/AstToCStar.ml` (the transformation from λow\* to C\*)
- **F\*:**
  the sources of F\* are in `FStar/src`


## Running functional tests

The tests that best showcase our methodology are run via `make -C
hacl-star/test extract-c`. This targets extracts to C code our AEAD development,
along with a variety of cryptographic algorithms (x25519, poly1305, chacha20,
xsalsa20); this target also compiles and runs test executables such as
`secure_api/krml-test-{vale,hacl}.exe`.

Additional test targets not covered by `make -C hacl-star/test extract-c`
include:
- `make -C hacl-star/code/poly1305 poly1305.exe`: unit test for the Poly1305
  algorithm
- `make -C hacl-star/code/salsa-family chacha20.exe salsa20.exe`: unit test for
  the Chacha20 and Salsa20 algorithms.


## Running performance tests

### With GCC

One can extract HACL\* to a releasable set of C files, then run a
performance benchmark using GCC, then show the performance results,
via:

```
make -C hacl-star/test snapshot-gcc
make -C hacl-star/test perf-gcc
cat hacl-star/test/benchmark-gcc.txt
```

In the above sequence, `gcc` can be replaced with `gcc-unrolled` to have
KaRaMeL unroll some loops when extracting the C code.

### With CompCert

Due to licensing reasons, we do not believe we can safely redistribute CompCert.
However, one can easily install CompCert via (Linux):

```
wget http://compcert.inria.fr/release/compcert-3.0.1.tgz
tar xzvf compcert-3.0.1.tgz
cd CompCert-3.0.1
./configure x86_64-linux
make -j 8
sudo make install
cd ..
```

Once this is done, the following series of commands will run performance
benchmarks for CompCert:

```
make -C hacl-star/test snapshot-ccomp
make -C hacl-star/test perf-ccomp
cat hacl-star/test/benchmark-compcert.txt
```

### Via the OpenSSL engine

A popular benchmarking tool is the OpenSSL "speed" command, which measures how
many operations of a given kind may be performed over a span of 3 seconds, for
different input sizes.

We wrote a new OpenSSL engine that packages some of our algorithms, meaning we
can measure their performance using the aforementioned testing framework. Right
now, the engine is set up so that our algorithms perform as many computations as
the OpenSSL ones, but due to some minor API differences, there remains some work
to ensure we compute the right result (e.g. detect when to perform the call to
Poly1305_Finalize according to the state machine of OpenSSL).

After regenerating the GCC snapshot by `make -C hacl-star/test snapshot-gcc`,
these OpenSSL engine tests can be run via `make -C hacl-star/test/openssl-engine test`.


## Replaying the proofs

One can replay the proofs by running the high-level command: `./everest verify
-j 8` where `8` is a suggested number of cores to use. One may want to allocate
more cores and more memory to their Docker instance if applicable.
