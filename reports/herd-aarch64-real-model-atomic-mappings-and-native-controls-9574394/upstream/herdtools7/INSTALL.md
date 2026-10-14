Binary installation with OPAM
=======================

[Install OPAM](https://opam.ocaml.org/doc/Install.html), then:

    % opam install herdtools7

Then, to get the newest version:

    % opam update
    % opam upgrade

Source build
============

Requirements
------------

- OCaml (version >= 4.14.0)
- dune (version >= 3.14.0)
- menhir (version >= 20231231)
- zarith
- logs

We strongly recommend to have this base software installed through the opam
package manager. This means an opam switch needs to be prepared before
installing the dependencies of the project. For example:

    % opam switch create herdtools7 --empty
    % eval $(opam config env --switch=herdtool7 --set-switch)
    % opam install . --deps-only

Notice: Compilation with ocamlbuild is not longer possible

Build
-----

    % make all

Testing
-------

The optional dependency `qcheck` can be installed with `opam` as follows:

    % opam install qcheck

Whether or not optional dependencies are installed, the following command
runs the tests, skipping the ones that necessitate non-available dependencies.

    % make test

More information on running more kinds of tests can be found at
[README-tests.md](README-tests.md)

Install
-------

Tools will be installed in PREFIX/bin, and various files in PREFIX/share/herdtools7.
By default (see Makefile) PREFIX is $HOME.
You can change PREFIX by editing the Makefile, or by explicitly defining it
when calling `make`, like so:

    % make PREFIX="$HOME/.local/" install
