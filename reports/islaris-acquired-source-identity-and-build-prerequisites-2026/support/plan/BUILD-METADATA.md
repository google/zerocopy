# Selected build and external-dependency metadata

Exact native `opam show --raw` fields from the published solution. These are commands/filters to inspect, not commands executed in this preparation. All 35 roots and every selected package declaring depexts are retained below. Full unfiltered raw metadata remains canonical.

## conf-pkg-config.5

```opam
build: [
  ["pkg-config" "--help"]
    {os != "win32" & !(os = "macos" & os-distribution = "homebrew")}
  ["pkgconf" "--version"]
    {os = "win32" & os-distribution != "msys2" |
     os = "macos" & os-distribution = "homebrew"}
  [
    "sh"
    "./write-config.sh"
    name
    "-v"
    "command:list"
    "EOL"
    "pkg-config"
      {os != "win32" & !(os = "macos" & os-distribution = "homebrew")}
    "pkgconf"
      {os = "win32" & os-distribution != "msys2" |
       os = "macos" & os-distribution = "homebrew"}
    "i686-w64-mingw32-pkgconf"
      {os = "win32" & os-distribution = "msys2" & host-arch-x86_32:installed}
    "--personality=i686-w64-mingw32"
      {os = "win32" & os-distribution = "cygwin" & host-arch-x86_32:installed}
    "x86_64-w64-mingw32-pkgconf"
      {os = "win32" & os-distribution = "msys2" & host-arch-x86_64:installed}
    "--personality=x86_64-w64-mingw32"
      {os = "win32" & os-distribution = "cygwin" & host-arch-x86_64:installed}
    "EOL"
  ]
  ["sh" "./install-shim.sh" name "pkgconf" bin]
    {os = "win32" & os-distribution = "cygwin"}
]

depexts: [
  ["pkg-config"] {os-family = "debian" | os-family = "ubuntu"}
  ["pkgconf"] {os-distribution = "arch"}
  ["pkgconf-pkg-config"] {os-family = "fedora"}
  ["pkgconfig"] {os-distribution = "centos" & os-version <= "7"}
  ["pkgconf-pkg-config"] {os-distribution = "mageia"}
  ["pkgconfig"] {os-distribution = "rhel" & os-version <= "7"}
  ["pkgconfig"] {os-distribution = "ol" & os-version <= "7"}
  ["pkgconf"] {os-distribution = "alpine"}
  ["pkg-config"] {os-distribution = "nixos"}
  ["pkgconf"] {os = "macos" & os-distribution = "homebrew"}
  ["pkgconfig"] {os = "macos" & os-distribution = "macports"}
  ["pkgconf"] {os = "freebsd"}
  ["pkgconf-pkg-config"] {os-distribution = "rhel" & os-version >= "8"}
  ["pkgconf-pkg-config"] {os-distribution = "centos" & os-version >= "8"}
  ["pkgconf-pkg-config"] {os-distribution = "ol" & os-version >= "8"}
  ["system:pkgconf"] {os = "win32" & os-distribution = "cygwinports"}
  ["pkgconf"] {os-distribution = "cygwin"}
]
```

## conf-findutils.1

```opam
build: ["sh" "-exc" "find . -name ."]

depexts: [
  ["findutils"] {os-family = "debian"}
  ["findutils"] {os-family = "ubuntu"}
  ["findutils"] {os-family = "fedora"}
  ["findutils"] {os-distribution = "rhel"}
  ["findutils"] {os-distribution = "centos"}
  ["findutils"] {os-distribution = "alpine"}
  ["findutils"] {os-distribution = "nixos"}
  ["findutils"] {os-family = "suse" | os-family = "opensuse"}
  ["findutils"] {os-distribution = "ol"}
  ["findutils"] {os-distribution = "arch"}
  ["system:findutils"] {os = "win32" & os-distribution = "cygwinports"}
  ["findutils"] {os-distribution = "cygwin"}
  ["findutils"] {os-distribution = "msys2"}
]
```

## ocaml-option-flambda.1 (exact root)

```opam
# No build/install/depext/patch/substitution fields
```

## conf-gmp.5

```opam
build: [
  [
    "sh"
    "-c"
    "pkg-config --print-errors --exists gmp || cc -c $CFLAGS -I/usr/local/include test.c"
  ] {os != "win32"}
  [
    "sh"
    "-exc"
    "$(ocamlc -config-var c_compiler) -c $CFLAGS -I/usr/local/include test.c"
  ] {os = "win32" & os-distribution = "cygwinports"}
  [
    "sh"
    "-exc"
    "%{host-arch-x86_64:installed?x86_64:}%%{host-arch-x86_32:installed?i686:}%-w64-mingw32-gcc -c $CFLAGS test.c"
  ] {os = "win32" & os-distribution != "cygwinports"}
]

depexts: [
  ["libgmp-dev"] {os-family = "debian"}
  ["libgmp-dev"] {os-family = "ubuntu"}
  ["gmp"] {os = "macos" & os-distribution = "homebrew"}
  ["gmp"] {os-distribution = "macports" & os = "macos"}
  ["gmp" "gmp-devel"] {os-distribution = "centos"}
  ["gmp" "gmp-devel"] {os-family = "fedora" | os-family = "fedora"}
  ["gmp" "gmp-devel"] {os-distribution = "ol"}
  ["gmp"] {os = "openbsd"}
  ["gmp"] {os = "freebsd"}
  ["gmp"] {os-distribution = "arch"}
  ["gmp-dev"] {os-distribution = "alpine"}
  ["gmp-devel"] {os-family = "suse" | os-family = "opensuse"}
  ["gmp"] {os = "win32" & os-distribution = "cygwinports"}
  ["gmp"] {os-distribution = "nixos"}
  ["libgmp-devel"] {os-family = "altlinux"}
]
```

## conf-linux-libc-dev.0

```opam
build: [
  ["sh" "-exc" "echo '#include <linux/stddef.h>' > test.c"]
  ["cc" "-E" "test.c"]
]

depexts: [
  ["linux-libc-dev"] {os-family = "debian"}
  ["linux-libc-dev"] {os-family = "ubuntu"}
  ["linux-glibc-devel"] {os-family = "suse" | os-family = "opensuse"}
  ["kernel-headers"]
    {os-family = "fedora" | os-distribution = "rhel" |
     os-distribution = "centos" |
     os-distribution = "ol"}
  ["linux-headers"] {os-family = "alpine"}
  ["linux-api-headers"] {os-family = "arch"}
]
```

## conf-zlib.1

```opam
build: [
  "pkgconf" {os = "win32" & os-distribution != "cygwinports"}
  "pkg-config" {os != "win32" | os-distribution = "cygwinports"}
  "--personality=i686-w64-mingw32"
    {os = "win32" & os-distribution != "cygwinports" &
     host-arch-x86_32:installed}
  "--personality=x86_64-w64-mingw32"
    {os = "win32" & os-distribution != "cygwinports" &
     host-arch-x86_64:installed}
  "zlib"
]

depexts: [
  ["zlib-dev"] {os-distribution = "alpine"}
  ["zlib1g-dev"] {os-family = "debian"}
  ["zlib1g-dev"] {os-family = "ubuntu"}
  ["zlib-devel" "zlib-static"]
    {os-distribution = "centos" & os-version < "10"}
  ["zlib-ng-compat-devel" "zlib-ng-compat-static"]
    {os-distribution = "centos" & os-version >= "10"}
  ["zlib-devel"] {os-family = "fedora" & os-version < "40"}
  ["zlib-ng-compat-devel" "zlib-ng-compat-static"]
    {os-family = "fedora" & os-version >= "40"}
  ["zlib-devel"] {os-distribution = "ol"}
  ["zlib"] {os-distribution = "nixos"}
  ["zlib"] {os-distribution = "homebrew" & os = "macos"}
  ["zlib"] {os-family = "arch"}
  ["zlib"] {os = "win32" & os-distribution = "cygwinports"}
  ["zlib-devel"] {os = "cygwin"}
  ["zlib-ng-compat-devel"] {os-family = "opensuse"}
  ["zlib-devel"] {os-family = "suse" & os-version < "16"}
  ["zlib-ng-compat-devel"] {os-family = "suse" & os-version >= "16"}
]
```

## ocaml-variants.4.14.0+options (exact root)

```opam
setenv: CAML_LD_LIBRARY_PATH = "%{lib}%/stublibs"

build: [
  [
    "./configure"
    "--host=x86_64-pc-windows"
      {system-msvc:installed & arch-x86_64:installed}
    "--host=x86_64-w64-mingw32"
      {os-distribution = "cygwin" & system-mingw:installed &
       arch-x86_64:installed}
    "--host=i686-pc-windows" {system-msvc:installed & arch-x86_32:installed}
    "--host=i686-w64-mingw32"
      {os-distribution = "cygwin" & system-mingw:installed &
       arch-x86_32:installed}
    "--prefix=%{prefix}%"
    "--docdir=%{doc}%/ocaml"
    "--with-flexdll=%{flexdll:share}%" {os = "win32" & flexdll:installed}
    "-C"
    "--with-afl" {ocaml-option-afl:installed}
    "--disable-native-compiler" {ocaml-option-bytecode-only:installed}
    "--disable-force-safe-string"
      {ocaml-option-default-unsafe-string:installed}
    "DEFAULT_STRING=unsafe" {ocaml-option-default-unsafe-string:installed}
    "--disable-flat-float-array" {ocaml-option-no-flat-float-array:installed}
    "--enable-flambda" {ocaml-option-flambda:installed}
    "--enable-frame-pointers" {ocaml-option-fp:installed}
    "--disable-naked-pointers" {ocaml-option-nnp:installed}
    "--enable-naked-pointers-checker" {ocaml-option-nnpchecker:installed}
    "CC=cc"
      {!ocaml-option-32bit:installed & !ocaml-option-musl:installed &
       (os = "openbsd" | os = "macos")}
    "CC=musl-gcc" {ocaml-option-musl:installed & os-distribution != "alpine"}
    "CFLAGS=-Os" {ocaml-option-musl:installed}
    "CC=gcc -m32" {ocaml-option-32bit:installed & os = "linux"}
    "CC=gcc -Wl,-read_only_relocs,suppress -arch i386 -m32"
      {ocaml-option-32bit:installed & os = "macos"}
    "ASPP=cc -c"
      {!ocaml-option-32bit:installed & !ocaml-option-musl:installed &
       (os = "openbsd" | os = "macos")}
    "ASPP=musl-gcc -c"
      {ocaml-option-musl:installed & os-distribution != "alpine"}
    "ASPP=gcc -m32 -c" {ocaml-option-32bit:installed & os = "linux"}
    "ASPP=gcc -arch i386 -m32 -c"
      {ocaml-option-32bit:installed & os = "macos"}
    "AS=as --32" {ocaml-option-32bit:installed & os = "linux"}
    "AS=as -arch i386" {ocaml-option-32bit:installed & os = "macos"}
    "--host=i386-linux" {ocaml-option-32bit:installed & os = "linux"}
    "--host=i386-apple-darwin13.2.0"
      {ocaml-option-32bit:installed & os = "macos"}
    "PARTIALLD=ld -r -melf_i386"
      {ocaml-option-32bit:installed & os = "linux"}
    "LIBS=-static" {ocaml-option-static:installed}
  ]
  [make "-j%{jobs}%"]
]

install: [make "install"]

build-env: MSYS2_ARG_CONV_EXCL = "*"
```

## dune.3.9.1 (exact root)

```opam
build: [
  ["ocaml" "boot/bootstrap.ml" "-j" jobs]
  [
    "./_boot/dune.exe"
    "build"
    "dune.install"
    "--release"
    "--profile"
    "dune-bootstrap"
    "-j"
    jobs
  ]
]
```

## sail_manifest.0.17 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  [
    "dune"
    "build"
    "-p"
    name
    "-j"
    jobs
    "--promote-install-files=false"
    "@install"
    "@runtest" {with-test}
    "@doc" {with-doc}
  ]
  ["dune" "install" "-p" name "--create-install-files" name]
]
```

## ordering.3.9.1 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  ["rm" "-rf" "vendor/csexp"]
  ["rm" "-rf" "vendor/pp"]
  ["dune" "build" "-p" name "-j" jobs "@install" "@doc" {with-doc}]
]
```

## coq-core.8.19.0 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  [
    "./configure"
    "-prefix"
    prefix
    "-mandir"
    man
    "-libdir"
    "%{lib}%/coq"
    "-native-compiler"
    "yes" {coq-native:installed}
    "no" {!coq-native:installed}
  ]
  [
    "dune"
    "build"
    "-p"
    name
    "-j"
    jobs
    "--promote-install-files=false"
    "@install"
    "@runtest" {with-test}
    "@doc" {with-doc}
  ]
  ["dune" "install" "-p" name "--create-install-files" name]
]

build-env: OCAMLPARAM = "_,w=-46,warn-error=-a,keywords=5.2"
```

## dyn.3.9.1 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  ["rm" "-rf" "vendor/csexp"]
  ["rm" "-rf" "vendor/pp"]
  ["dune" "build" "-p" name "-j" jobs "@install" "@doc" {with-doc}]
]
```

## coqide-server.8.19.0 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  [
    "dune"
    "build"
    "-p"
    name
    "-j"
    jobs
    "--promote-install-files=false"
    "@install"
    "@runtest" {with-test}
    "@doc" {with-doc}
  ]
  ["dune" "install" "-p" name "--create-install-files" name]
]
```

## coq-stdlib.8.19.0 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  [make "dunestrap" "COQ_DUNE_EXTRA_OPT=-split" "DUNESTRAPOPT=-p coq-stdlib"]
  [
    "dune"
    "build"
    "-p"
    name
    "-j"
    jobs
    "--promote-install-files=false"
    "@install"
    "@runtest" {with-test}
    "@doc" {with-doc}
  ]
  ["dune" "install" "-p" name "--create-install-files" name]
]
```

## stdune.3.9.1 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  ["rm" "-rf" "vendor/csexp"]
  ["rm" "-rf" "vendor/pp"]
  ["dune" "build" "-p" name "-j" jobs "@install" "@doc" {with-doc}]
]
```

## isla-lang.dev (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  [
    "dune"
    "build"
    "-p"
    name
    "-j"
    jobs
    "@install"
    "@runtest" {with-test}
    "@doc" {with-doc}
  ]
]
```

## coq.8.19.0 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  [
    "dune"
    "build"
    "-p"
    name
    "-j"
    jobs
    "--promote-install-files=false"
    "@install"
    "@doc" {with-doc}
  ]
  ["dune" "install" "-p" name "--create-install-files" name]
]
```

## dune-private-libs.3.9.1 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  ["rm" "-rf" "vendor/csexp"]
  ["rm" "-rf" "vendor/pp"]
  ["dune" "build" "-p" name "-j" jobs "@install" "@doc" {with-doc}]
]
```

## coq-stdpp.dev.2024-09-10.3.a1a12e00 (exact root)

```opam
build: ["./make-package" "stdpp" "-j%{jobs}%"]

install: ["./make-package" "stdpp" "install"]
```

## coq-record-update.0.3.3 (exact root)

```opam
build: [make "-j%{jobs}%" "NO_TEST=1"]

install: [make "install"]
```

## coq-bbv.1.5 (exact root)

```opam
build: [make "-j%{jobs}%"]

install: [make "install"]
```

## dune-site.3.9.1 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  ["rm" "-rf" "vendor/csexp"]
  ["rm" "-rf" "vendor/pp"]
  ["dune" "build" "-p" name "-j" jobs "@install" "@doc" {with-doc}]
]
```

## coq-stdpp-bitvector.dev.2024-09-10.3.a1a12e00 (exact root)

```opam
build: ["./make-package" "stdpp_bitvector" "-j%{jobs}%"]

install: ["./make-package" "stdpp_bitvector" "install"]
```

## coq-iris.dev.2024-09-10.1.6f24ed4b (exact root)

```opam
build: ["./make-package" "iris" "-j%{jobs}%"]

install: ["./make-package" "iris" "install"]
```

## coq-sail.0.17 (exact root)

```opam
build: [make "-C" "src" "HAVE_OPAM_BBV=yes"]

install: [make "-C" "src" "install"]
```

## libsail.0.17 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  [
    "dune"
    "build"
    "-p"
    name
    "-j"
    jobs
    "--promote-install-files=false"
    "@install"
    "@runtest" {with-test}
    "@doc" {with-doc}
  ]
  ["dune" "install" "-p" name "--create-install-files" name]
]
```

## coq-stdpp-unstable.dev.2024-09-10.3.a1a12e00 (exact root)

```opam
build: ["./make-package" "stdpp_unstable" "-j%{jobs}%"]

install: ["./make-package" "stdpp_unstable" "install"]
```

## sail_sv_backend.0.17 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  [
    "dune"
    "build"
    "-p"
    name
    "-j"
    jobs
    "--promote-install-files=false"
    "@install"
    "@runtest" {with-test}
    "@doc" {with-doc}
  ]
  ["dune" "install" "-p" name "--create-install-files" name]
]
```

## sail_smt_backend.0.17 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  [
    "dune"
    "build"
    "-p"
    name
    "-j"
    jobs
    "--promote-install-files=false"
    "@install"
    "@runtest" {with-test}
    "@doc" {with-doc}
  ]
  ["dune" "install" "-p" name "--create-install-files" name]
]
```

## sail_output.0.17 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  [
    "dune"
    "build"
    "-p"
    name
    "-j"
    jobs
    "--promote-install-files=false"
    "@install"
    "@runtest" {with-test}
    "@doc" {with-doc}
  ]
  ["dune" "install" "-p" name "--create-install-files" name]
]
```

## sail_ocaml_backend.0.17 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  [
    "dune"
    "build"
    "-p"
    name
    "-j"
    jobs
    "--promote-install-files=false"
    "@install"
    "@runtest" {with-test}
    "@doc" {with-doc}
  ]
  ["dune" "install" "-p" name "--create-install-files" name]
]
```

## sail_lem_backend.0.17 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  [
    "dune"
    "build"
    "-p"
    name
    "-j"
    jobs
    "--promote-install-files=false"
    "@install"
    "@runtest" {with-test}
    "@doc" {with-doc}
  ]
  ["dune" "install" "-p" name "--create-install-files" name]
]
```

## sail_latex_backend.0.17 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  [
    "dune"
    "build"
    "-p"
    name
    "-j"
    jobs
    "--promote-install-files=false"
    "@install"
    "@runtest" {with-test}
    "@doc" {with-doc}
  ]
  ["dune" "install" "-p" name "--create-install-files" name]
]
```

## sail_doc_backend.0.17 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  [
    "dune"
    "build"
    "-p"
    name
    "-j"
    jobs
    "--promote-install-files=false"
    "@install"
    "@runtest" {with-test}
    "@doc" {with-doc}
  ]
  ["dune" "install" "-p" name "--create-install-files" name]
]
```

## sail_coq_backend.0.17 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  [
    "dune"
    "build"
    "-p"
    name
    "-j"
    jobs
    "--promote-install-files=false"
    "@install"
    "@runtest" {with-test}
    "@doc" {with-doc}
  ]
  ["dune" "install" "-p" name "--create-install-files" name]
]
```

## sail_c_backend.0.17 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  [
    "dune"
    "build"
    "-p"
    name
    "-j"
    jobs
    "--promote-install-files=false"
    "@install"
    "@runtest" {with-test}
    "@doc" {with-doc}
  ]
  ["dune" "install" "-p" name "--create-install-files" name]
]
```

## sail.0.17 (exact root)

```opam
build: [
  ["dune" "subst"] {dev}
  [
    "dune"
    "build"
    "-p"
    name
    "-j"
    jobs
    "--promote-install-files=false"
    "@install"
    "@runtest" {with-test}
    "@doc" {with-doc}
  ]
  ["dune" "install" "-p" name "--create-install-files" name]
]

substs: "src/bin/manifest.ml"
```

## coq-lithium.dev.2024-09-11.0.7945a29d (exact root)

```opam
build: [
  ["dune" "subst"] {pinned}
  ["dune" "build" "-p" name "-j" jobs]
]
```

## coq-sail-riscv.0.5 (exact root)

```opam
build: [
  [make "ARCH=RV64" "riscv_coq_build"]
  [make "ARCH=RV32" "riscv_coq_build"]
]

install: [make "riscv_coq_install"]
```

## islaris.dev (exact root)

```opam
build: [
  ["dune" "subst"] {pinned}
  ["dune" "build" "-p" name "-j" jobs]
]
```
