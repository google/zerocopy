# -*- Makefile -*-

# --------------------------------------------------------------------
JSJOBS    ?= 2
CHECKPY   ?=
CHECK     := $(CHECKPY) scripts/runtest --jobs="$(JSJOBS)"
CHECK     += config/tests.config
CHECKCATS ?= \
	x86-64-ATT \
	x86-64-Intel \
	x86-64-nolea \
	x86-64-windows \
	arm-m4 \
	armv8a \
	risc-v \
	x86-64-stack-zero-loop \
	x86-64-stack-zero-unrolled \
	arm-m4-stack-zero-loop \
	arm-m4-stack-zero-unrolled \
	armv8a-stack-zero-loop \
	armv8a-stack-zero-unrolled \
	risc-v-stack-zero-loop \
	risc-v-stack-zero-unrolled \
	CCT CCT-riscv CCT-DOIT CCT-DOIT-riscv CCT-DOIT-arm-m4 SCT

# --------------------------------------------------------------------
DESTDIR  ?=
PREFIX   ?= /usr/local
BINDIR   := $(PREFIX)/bin
INSTALL  ?= install
DUNE_OPTS ?= --prefix $(PREFIX)

# --------------------------------------------------------------------
DISTDIR ?= jasmin-compiler

# --------------------------------------------------------------------
OBELISK ?= obelisk

# --------------------------------------------------------------------
.PHONY: all CIL check check-ci
.PHONY: clean install uninstall dist

all:
	$(RM) jasminc jasmin2tex jasmin-ct jasmin2ec jasmin-checksafety
	dune build @check @install
	for p in _build/install/default/bin/*; do ln -sf $$p $$(basename $$p); done

CIL:
	$(RM) -f src/CIL/*.ml src/CIL/*.mli ../proofs/extraction.vo
	$(MAKE) -C ../proofs extraction
	cp ../proofs/lang/ocaml/*.ml  src/CIL/
	cp ../proofs/lang/ocaml/*.mli src/CIL/

check: all check-ci

check-ci:
	$(CHECK) --report=report.log $(CHECKCATS)

check-ec:
	$(MAKE) -C examples/gimli/proofs
	$(MAKE) -C examples/extraction-unit-tests

check-all: check
	dune runtest -f

clean:
	dune clean
	$(RM) jasminc jasmin2tex jasmin-ct jasmin2ec jasmin-checksafety

install:
	dune install $(DUNE_OPTS)

uninstall:
	dune uninstall $(DUNE_OPTS)

# --------------------------------------------------------------------
dist: $(DISTDIR).tgz

$(DISTDIR).tgz: MANIFEST
	$(RM) -r $(DISTDIR)
	../scripts/distribution $(DISTDIR)/compiler $<
	cp -riv ../eclib $(DISTDIR)/
	cp ../Makefile.compiler $(DISTDIR)/Makefile
	cp jasmin.opam $(DISTDIR)/
	cp ../README.compiler.md $(DISTDIR)/README.md
	cp ../LICENSE $(DISTDIR)/
	tar -czvf $(DISTDIR).tgz --owner=0 --group=0 $(DISTDIR)
	$(RM) -r $(DISTDIR)

# --------------------------------------------------------------------
jasmin.bnf: src/parser.mly
	$(OBELISK) -i -o $@ $<

jasmin.ebnf: scripts/expand-bnf jasmin.bnf
	@sed -f $^ > $@
