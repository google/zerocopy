KaRaMeL
-------

| Linux  |
|---------|
[![CI](https://github.com/FStarLang/karamel/actions/workflows/ci.yml/badge.svg)](https://github.com/FStarLang/karamel/actions/workflows/ci.yml)

KaRaMeL (formerly known as KReMLin) is a tool that extracts an F\* program to
readable C code: K&R meets ML!

If the F\* program verifies against a low-level memory model that talks about
the stack and the heap; if it is first-order; if it obeys certain restrictions
(e.g. non-recursive data types) then KaRaMeL will turn it into C.

The best way to learn about KaRaMeL is its work-in-progress
[tutorial](https://fstarlang.github.io/lowstar/html/). Pull requests and
feedback are welcome!

- [DESIGN.md](DESIGN.md) has a technical overview of the different
  transformation passes performed by KaRaMeL, and is slightly out of date.

This work has been formalized on paper. We state that the compilation of
such F\* programs to C preserves semantics. We start from Low\*, a subset of
F\*, and relate its semantics to [CompCert](http://compcert.inria.fr/)'s Clight.
- the [ICFP 2017 Paper] provides an overview of KaRaMeL as well
  as a paper formalization of our compilation toolchain

We have written 120,000 lines of Low\* code, implementing the [TLS
1.3](https://tlswg.github.io/tls13-spec/) record layer. As such, KaRaMeL is a
key component of [Project Everest](https://project-everest.github.io/).
- [HACL\*], our High Assurance Crypto Library, provides numerous cryptographic
  primitives written in F\*; these primitives enjoy memory safety, functional
  correctness, and some degree of side-channel resistance -- they extract to C
  via KaRaMeL.

[ML Workshop Paper]: https://jonathan.protzenko.fr/papers/ml16.pdf
[HACL\*]: https://github.com/hacl-star/hacl-star
[ICFP 2017 Paper]: https://arxiv.org/abs/1703.00053

## Trying out KaRaMeL

KaRaMeL requires OCaml (>= 4.10.0), OPAM, and a recent version of GNU make.

**Regarding GNU make:** On OSX, this may require you to install a recent GNU
make via homebrew, and invoke `gmake` instead of `make`.

**Regarding OCaml:** Install OPAM via your package manager, then:

`$ opam install ppx_deriving_yojson zarith pprint "menhir>=20161115" sedlex process fix "wasm>=2.0.0" visitors ctypes-foreign ctypes uucp`

Next, make sure you have an up-to-date F\*, either as a binary package
or that you have built it by running `make`. The `fstar.exe` executable
should be on your PATH, or you may set the variable `FSTAR_EXE` to its
location.

To build just run `make` from this directory.

**Note:** on OSX, KaRaMeL is happier if you have `greadlink` installed (`brew
install coreutils`).

If you have the right version of F\* and `fstar.exe` is in your `PATH` then you
can run the KaRaMeL test suite by doing `make test`.

## Installing through OPAM

KaRaMeL is also available on OPAM, by running `opam install karamel`.

If you installed the latest version of F\* through OPAM, using `opam pin add fstar --dev-repo`,
you can also install the most up-to-date version of KaRaMeL by running `opam pin add karamel --dev-repo`.

File a bug if things don't work!

## Documentation

The `--help` flag contains a substantial amount of information.

```
$ ./krml --help
```

## License

KaRaMeL is released under the [Apache 2.0 license] and MIT license; see `LICENSE-*` for more details.

[Apache 2.0 license]: https://www.apache.org/licenses/LICENSE-2.0
