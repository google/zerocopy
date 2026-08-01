Independent adjudication:

| Vulnerable report | Discovery | Proposition | Dataflow | Authority | Valid use | Config | Class. | Total |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `n6a9.md` | 2 | 2 | 2 | 2 | 2 | 2 | 2 | **14/14** |
| `g2r6.md` | 2 | 2 | 2 | 1 | 2 | 1 | 2 | **12/14** |

- `n6a9.md` fully recovers the defect. It establishes the exact 1.84.1 proposition that `MaybeUninit::zeroed()` does not preserve padding on return, traces the false `Initialized` upgrade through `as_bytes` into an invalid `&mut [u8]`, supplies a valid padded `FromBytes` witness, and gives the decisive fully safe adversarial `Read` that inspects padding. Scope, classification, configuration closure, and the proof-documentation finding are all correct.
- `g2r6.md` also recovers the complete semantic vulnerability and safe adversarial path. Its hard error is traceability: every local citation targets out-of-scope `/u3c8`, not `a9n6`. Its `u8`/`u16` witness and configuration closure are also less fully authorized than `n6a9`’s explicit-alignment witness and cfg analysis. The conclusion remains correct.

Fixed reports:

- `w7f4.md`: **Pass.** It correctly proves that `uninit(); buf.zero()` performs a full-object `write_bytes` in the final storage, with no typed move before exposing the byte slice. Thus padding is initialized before arbitrary safe `Read` code may inspect it; success-without-writing, error, unwind, padding, and ZST paths remain sound. It also correctly separates implementation soundness from incomplete checked-in proof documentation.
- `j5h2.md`: **Technical pass, evidence defect.** Its reconstruction is sound and usefully explains that any later typed-move loss of padding is harmless once producing `Self`. However, all local links target `/h2j5`, not `f4w7`, which is a hard snapshot-binding error. It also omits the material documentation-maintenance finding identified by `w7f4`—the citation TODO, stale 1.81 authority, and missing local proof bridges.

The exact 1.84.1 documentation supports both central conclusions: returned `MaybeUninit::zeroed()` values need not retain initialized padding, while an in-place raw byte write initializes the entire backing range before the safe `Read` boundary.
