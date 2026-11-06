# Boogie

[![License][license-badge]](LICENSE.txt)
[![NuGet package][nuget-badge]][nuget]

Boogie is a modeling language, intended as a layer on
which to build program verifiers for other languages. Several program verifiers
have been built in this way, including the
[VCC](https://github.com/microsoft/vcc) and
[HAVOC](https://www.microsoft.com/en-us/research/project/havoc) verifiers for C
and the verifiers for [Dafny](https://github.com/dafny-lang/dafny),
[Chalice](https://www.microsoft.com/en-us/research/project/chalice),
[Spec#](https://www.microsoft.com/en-us/research/project/spec), 
and [Move](https://github.com/move-language/move).
For a sample verifier for a toy language built on top of Boogie, see
[Forro](https://github.com/boogie-org/forro).

Boogie is also the name of a tool. The tool accepts the Boogie language as
input, optionally infers some invariants in the given Boogie program, and then
generates verification conditions that are passed to an SMT solver. The default
SMT solver is [Z3](https://github.com/Z3Prover/z3).

A tutorial for Boogie is available [here](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml178.pdf).
The documentation in this tutorial, although slightly out-of-date, captures the essence of the Boogie language and tool.

Boogie has long been used for modeling and verifying sequential programs.
Recently, through its [Civl](https://civl-verifier.github.io/) extension, Boogie 
has become capable of modeling concurrent and distributed systems.

## Getting help

You can ask questions and report issues on our [issue tracker](https://github.com/boogie-org/boogie/issues).

## Contribute

We are happy to receive contributions via [pull requests](https://github.com/boogie-org/boogie/pulls).

## Dependencies

Boogie requires [.NET](https://dotnet.microsoft.com) and a supported SMT
solver (see [below](#backend-smt-solver)).

## Installation

Boogie releases are packaged as a .NET global tool available at
[nuget.org][nuget]. To install Boogie simply run:

```
$ dotnet tool install --global boogie
```

## Building

To build Boogie run:

```
$ dotnet build Source/Boogie.sln
```

The compiled Boogie binary is
`Source/BoogieDriver/bin/${CONFIGURATION}/${FRAMEWORK}/BoogieDriver`.

## Backend SMT Solver

The default SMT solver for Boogie is [Z3](https://github.com/Z3Prover/z3).
Support for [CVC5](https://cvc5.github.io/) and
[Yices2](https://yices.csl.sri.com/) is experimental.

By default, Boogie looks for an executable called `z3|cvc5|yices2[.exe]` in your
`PATH` environment variable. If the solver executable is called differently on
your system, use `/proverOpt:PROVER_NAME=<exeName>`. Alternatively, an explicit
path can be given using `/proverOpt:PROVER_PATH=<path>`.

To learn how custom options can be supplied to the SMT solver (and more), call
Boogie with `/proverHelp`.

### Z3

The current test suite assumes version 4.11.2, but earlier and newer versions may
also work.

### CVC5 (experimental)

Call Boogie with `/proverOpt:SOLVER=CVC5`.

### Yices2 (experimental)

Call Boogie with `/proverOpt:SOLVER=Yices2`.

Works for unquantified fragments, e.g. arrays + arithmetic + bitvectors. Does
not work for quantifiers, generalized arrays, datatypes.

## Testing

Boogie has two forms of tests: driver tests and unit tests.

### Driver tests

See the [Driver test documentation](Test/README.md)

### Unit tests

See the [Unit test documentation](Source/UnitTests/README.md)

## Versioning and Release

The current version of Boogie is noted in a [build property](Source/Directory.Build.props).
To push a new version to nuget, perform the following steps:

- Update the version (e.g., x.y.z) in `Source/Directory.Build.props`
- `git add Source/Directory.Build.props; git commit -m "Release version x.y.z"` to commit the change locally
- `git push origin master:release-vx.y.z` to push your change in a separate branch, where `origin` normally denotes the remote on github.com
- [Create a pull request](https://github.com/boogie-org/boogie/compare) and wait for it to be approved and merged
- `git tag vx.y.z` to create a local tag for the version
- `git push origin vx.y.z` to push the tag once the pull request is merged

The [CI workflow](.github/workflows/test.yml) will build and push the packages.

## License

Boogie is licensed under the MIT License (see [LICENSE.txt](LICENSE.txt)).

[license-badge]: https://img.shields.io/github/license/boogie-org/boogie?color=blue
[nuget]:         https://www.nuget.org/packages/Boogie
[nuget-badge]:   https://img.shields.io/nuget/v/Boogie
