# Upstream attribution and public projection

Upstream files are retained unchanged as evidence, with their original notices. [Source pointers](support/source-pointers.json), [notice pointers](support/notice-pointers.json) and the [attribution inventory](support/attribution-inventory.json) bind paths, fixed revisions or source checksums, Git blob identities, SHA256 hashes and lengths. Source files inside an archive are identified by the archive path and exact member name; their presence does not turn upstream text into report instructions.

## Fixed Git projects

The public audit projection includes complete README/Makefile files and selected Sail implementation files. These are the applicable exact project notice records, preserved from the same frozen revisions:

| Project and fixed revision | Redistributed material | Exact notice text |
|---|---|---|
| Sail `b14f649845db850b3673696e2aa90565fa2a60ef` | INSTALL, README, Makefile and selected lib/SMT implementation files from A17, including the exposed constraint.ml | [Historical LICENSE](support/source/old-sail/LICENSE), including copyright, acknowledgments, BSD two-clause terms, exclusions and disclaimers; implementation files retain their own notices |
| RISC-V Sail model `837ede9b39fae2aa97849da89c4b3b5a93344890` | A42 README and Makefile | [Historical LICENCE](support/source/old-riscv/LICENCE), including copyright, acknowledgments, BSD two-clause terms, exclusions and disclaimers |
| isla-lang `bda86c9f0bd28bbaa2481f50ddc986ede342805a` | A35 README and Makefile | [LICENSE](support/attribution-evidence/A35-LICENSE), BSD two-clause notice and contributors |
| stdpp `a1a12e00fba07f2e41ccd74a8b593b88e48fc2c3` | A36 README and Makefile | [LICENSE](support/attribution-evidence/A36-LICENSE), applying BSD three-clause terms to all files |
| Iris `6f24ed4baa4d61967a95bac834eab2c66f3b76fa` | A39 root README and Makefile | [LICENSE](support/attribution-evidence/A39-LICENSE) distinguishes everything outside docs/ and tex/ from documentation inside those directories; preserve both [LICENSE-CODE](support/attribution-evidence/A39-LICENSE-CODE) and [LICENSE-DOCS](support/attribution-evidence/A39-LICENSE-DOCS) |
| coq-sail `169934e27ceafe393ed4d365985f7b12d974d56e` | A40 README | [LICENSE](support/attribution-evidence/A40-LICENSE), Sail Coq support-library BSD two-clause notice |
| RefinedC/Lithium `7945a29d1647970709a9b5ad2ffc53c757e130cc` | A41 root README and Makefile | [LICENSE](support/attribution-evidence/A41-LICENSE), BSD terms applying except as otherwise noted; no linux/ files are copied here |
| Islaris `c978e10f50db5c40f0fdf113f5f76a779782c6f9` | A43 README and Makefile | [LICENSE](support/attribution-evidence/A43-LICENSE), BSD two-clause notice and named developers; the exact [THIRD_PARTY_FILES.md](support/attribution-evidence/A43-THIRD_PARTY_FILES.md) contains `None` followed by two newlines |

The first two notices have [Sail](support/license-provenance/sail-LICENSE.json) and [RISC-V](support/license-provenance/riscv-LICENCE.json) capture receipts. The additional nine root notice bodies have corresponding raw JSON/status/stderr receipts under support/attribution-evidence/. All were checked against fixed-tree blob identities, byte lengths and SHA256; newer licenses were not substituted.

## Metadata and six omitted external bodies

The exact main opam repository [README](support/notices/opam-repository/README.md) and [COPYING](support/notices/opam-repository/COPYING) at `56aefa37456aa263913289a4174daca01c4b9339` preserve CC0 1.0 for repository metadata and its collection. This is not asserted to license separately downloaded external bodies. The attribution inventory preserves each consuming package's original SPDX declaration as metadata, without treating it as a blanket license for external files.

All six raw external extra-source bodies are omitted under one public projection rule: A01 install-shim.sh, A02 write-config.sh, A03 test.c, A05 ocaml-variants.install, A06 ocaml-config.install and A07 gen_ocaml_config.ml.in. The [projection ledger](support/public-projection.json) binds exact member names, lengths, SHA256 hashes and the reason; there are no placeholders. Their source URLs, declared and observed hashes, metadata, consumer coverage, native check results and original independent review remain unchanged. The original review actually rehashed all six bodies; none of those raw bodies is now redistributed. This publication decision makes no conclusion about copyrightability, whether a license exists, or legal permission to redistribute. It avoids relying on a legal interpretation of unmarked external fragments or differing project/package declarations.

The report's own scripts, receipts and hash ledgers retain their provenance. Upstream ownership remains with the named projects and contributors; inclusion is evidence, not endorsement or a claim to upstream authorship. No complete source trees, OCI images or compiler/package binaries are included.
