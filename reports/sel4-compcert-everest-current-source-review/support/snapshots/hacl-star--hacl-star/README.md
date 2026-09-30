# A High-Assurance Cryptographic Library

This repository contains verified code for a library of modern
cryptographic algorithms, including Curve25519, Ed25519, AES-GCM,
Chacha20, Poly1305, SHA-2, SHA-3, HMAC, and HKDF. This set of algorithms
is enough to support the full NaCl API and several TLS 1.3 ciphersuites.
The code for all of these algorithms is formally verified using the
[F\*](https://fstar-lang.org/) verification framework for memory
safety, functional correctness, and secret independence (resistance to
some types of timing side-channels).

## Status

*Warning*: This is the research home of HACL\*. If you are looking for
documentation, releases, language bindings and code that can be satisfactorily
integrated into a production project, please check out [HACL
packages](https://github.com/cryspen/hacl-packages/).

The code in this repository is divided into three closely-related sub-projects,
all developed as part of [Project Everest](https://project-everest.github.io/).

We are actively developing and integrating our code on the
[main](https://github.com/project-everest/hacl-star/tree/main/)
branch, which tracks F\*'s `master` branch.

## HACL\*

[HACL\*](code/) is a formally verified library
of modern cryptographic algorithms written in a subset of
[F\*](https://fstarlang.github.io) called Low\* and compiled to C
using a compiler called
[KaRaMeL](https://github.com/FStarLang/karamel). The Low\* source code
for each primitive is verified for memory safety, functional
correctness, and secret independence. The compiler generates
efficient, readable, standalone C code for each algorithm that
can be easily integrated into any C project.  We include the current C code for various HACL\*
algorithms in the [dist](dist/) directory. HACL\* can also be compiled to WebAssembly.

## ValeCrypt

[ValeCrypt](vale/) provides formally verified high-performance
cryptographic code for selected primitives in assembly language. It relies on the
[Vale tool](https://github.com/project-everest/vale) to produce
code and proofs in [F\*](https://github.com/FStarLang/FStar). Vale supports
multiple platforms and proves that its implementations are memory safe,
functionally correct, and that timing and memory accesses are secret
independent.

## EverCrypt

[EverCrypt](providers/evercrypt/) is a high-performance, cross-platform, formally
verified modern cryptographic provider that packages implementations from
HACL\* and ValeCrypt, and automatically picks the fastest one available,
depending on processor support and the target execution environment
(*multiplexing*). Furthermore, EverCrypt offers an (*agile*) API that makes it
simple to switch between algorithms (e.g., from SHA2 to SHA3).

## Citing HACL*

If you want to cite HACL\* in a research publication, here is some guidance to
make sure you pick the right publications.

- For HACL* in its current incarnation, including SIMD versions of algorithms: CCS'20.

```
@inproceedings{polubelova2020haclxn,
  title={{HACLxN}: Verified generic {SIMD} crypto (for all your favourite platforms)},
  author={Polubelova, Marina and Bhargavan, Karthikeyan and Protzenko, Jonathan and Beurdouche, Benjamin and Fromherz, Aymeric and Kulatova, Natalia and Zanella-B{\'e}guelin, Santiago},
  booktitle={Proceedings of the 2020 ACM SIGSAC Conference on Computer and Communications Security},
  pages={899--918},
  year={2020}
}
```

- For HACL* in general (discouraged, since none of that code exists anymore): CCS'17

```
@inproceedings{zinzindohoue2017hacl,
  title={{HACL*}: A verified modern cryptographic library},
  author={Zinzindohou{\'e}, Jean-Karim and Bhargavan, Karthikeyan and Protzenko, Jonathan and Beurdouche, Benjamin},
  booktitle={Proceedings of the 2017 ACM SIGSAC Conference on Computer and Communications Security},
  pages={1789--1806},
  year={2017}
}
```

- For EverCrypt, the agile, multiplexing, CPU-detecting API on top of HACL\*: S&P'20

```
@inproceedings{protzenko2020evercrypt,
  title={Evercrypt: A fast, verified, cross-platform cryptographic provider},
  author={Protzenko, Jonathan and Parno, Bryan and Fromherz, Aymeric and Hawblitzel, Chris and Polubelova, Marina and Bhargavan, Karthikeyan and Beurdouche, Benjamin and Choi, Joonwon and Delignat-Lavaud, Antoine and Fournet, C{\'e}dric and others},
  booktitle={2020 IEEE Symposium on Security and Privacy (SP)},
  pages={983--1002},
  year={2020},
  organization={IEEE}
}
```

- For HACL-WASM, the WebAssembly backend of HACL\*: S&P'19

```
@inproceedings{protzenko2019formally,
  title={Formally verified cryptographic web applications in {WebAssembly}},
  author={Protzenko, Jonathan and Beurdouche, Benjamin and Merigoux, Denis and Bhargavan, Karthikeyan},
  booktitle={2019 IEEE Symposium on Security and Privacy (SP)},
  pages={1256--1274},
  year={2019},
  organization={IEEE}
}
```

- For the HACL streaming APIs with heap-allocated state and internal buffering (hashes, MACs): ICFP'23

```
@article{ho2023modularity,
  title={Modularity, Code Specialization, and Zero-Cost Abstractions for Program Verification},
  author={Ho, Son and Fromherz, Aymeric and Protzenko, Jonathan},
  journal={Proceedings of the ACM on Programming Languages},
  volume={7},
  number={ICFP},
  pages={385--416},
  year={2023},
  publisher={ACM New York, NY, USA}
}
```

## License

All the code in this repository is released under an Apache 2.0 license.
The generated C code from HACL\* is also released under an MIT license.
Contact the maintainers if you have other licensing requirements.

## Contact or Contribute

This repository contains contributions from many students and researchers at INRIA, Microsoft Research, and Carnegie Mellon University,
and it is under active development. The primary authors of each verified algorithm are noted in the corresponding AUTHORS.md file.
For questions and comments, or if you want to contribute to the project, contact the current maintainers at hacl-star-maintainers@inria.fr.
