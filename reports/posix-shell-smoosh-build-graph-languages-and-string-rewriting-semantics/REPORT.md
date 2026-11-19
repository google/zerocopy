# POSIX Shell (Smoosh), Build-Graph Languages, Tcl EIAS, and Emacs Lisp Dynamic Scope Semantics

## Summary

Command shells, build-graph DSLs, macro preprocessors, and extensible editor/scripting runtimes share a common semantic architecture that violates standard lexically scoped, statically phased AST assumptions: **phased string rewriting interleaved with operating-system or environment state**. Across these systems, parsing, substitution, field/list splitting, evaluation, and OS side effects occur across multiple coupled stages whose boundaries are frequently dynamic or context-sensitive:

1. **POSIX Shell & Smoosh (`mgree/smoosh`)**: POSIX.1-2024 defines a seven-step word-expansion pipeline (tilde, parameter, command substitution, arithmetic, `$IFS` field splitting, pathname globbing, quote removal) coupled to an OS process model (`fork`, pipes, file descriptors, traps). Smoosh formalizes this as a small-step operational semantics parameterized over an abstract `OS` typeclass (`os_symbolic` vs `os_system`), capturing non-compositional behaviors such as dynamic `set -e` (`CheckedExit`) suppression across functions and subshells on the left of `||`/`&&`/conditionals, asymmetric trailing-delimiter elision in `$IFS` splitting, pipeline subshell state loss, and trap-delivery windows.
2. **Build-Graph & Macro Systems (GNU Make, CMake, GNU M4/Autoconf)**: GNU Make splits execution into **Stage 1** (makefile read-in: immediate expansion of `:=`, conditionals, target/prerequisite lists, and `$(eval)` graph mutation) and **Stage 2** (DAG traversal: deferred recursive expansion of `=`, target-specific variables, `.SECONDEXPANSION`, and per-line shell recipes). CMake introduces a **three-stage** split (configure-time `;`-delimited string lists in `cmList`, generate-time `$<...>` generator expressions in `cmGeneratorExpression`, and build-time backend DAG). GNU M4 performs eager argument expansion with stack-pushed input rescanning where each expansion strips one quote layer, requiring Autoconf M4sugar (`m4_defun`/`m4_require`) to implement a diversion-stack topological scheduler inside text rewriting.
3. **Tcl Everything-Is-A-String (EIAS)**: Tcl's 12-rule syntax (*Dodekalogue*, `doc/Tcl.n`) performs a single left-to-right substitution pass with no re-parsing of substituted text (except explicit `{*}` expansion or `eval`). Semantics are defined over strings, while performance relies on dual-ported `Tcl_Obj` values caching a mutable `(typePtr, internalRep)` alongside a UTF-8 `bytes` representation; alternating incompatible type interpretations on a shared `Tcl_Obj` triggers **shimmering**, repeatedly invoking `freeIntRepProc` and `setFromAnyProc` and potentially degrading $O(1)$ operations to $O(N)$ re-parsing.
4. **GNU Emacs Lisp**: Symbols carry a 2-bit `redirect` discriminator (`SYMBOL_PLAINVAL`, `SYMBOL_VARALIAS`, `SYMBOL_LOCALIZED`, `SYMBOL_FORWARDED`) and a `declared_special` bit. Even in files with `lexical-binding: t`, `defvar`-declared symbols bind dynamically on the C `specpdl` unwind stack. Buffer-local variables (`Lisp_Buffer_Local_Value`) interact non-intuitively with `let` (`specbind`): binding a variable that lacks a local value in the current buffer emits `SPECPDL_LET_DEFAULT`, mutating the global default across all buffers without local bindings, while binding an existing local value emits `SPECPDL_LET_LOCAL` pinned to `where.buf` so switching buffers inside `let` leaves the new buffer's value untouched. Function advice (`nadvice.el`) rewrites symbol function cells via combinator closures, which can be bypassed by byte-compiler inlining (`defsubst`, compiler macros) or direct C subr calls.

## Applicability

This report synthesizes normative standards, pinned upstream source code, peer-reviewed formalization, and local runtime probes to provide a unified semantic reference for static analyzers, verification tools, FFI/build-orchestration wrappers, and compiler front-ends that generate, parse, or reason about shell scripts, build files, macro expansions, Tcl scripts, or Emacs Lisp extensions.

- **Subject relationships**:
  - **POSIX.1-2024 (Issue 8)** serves as the normative specification for shell syntax, word expansion, pipelines, `set -e`, `pipefail`, and shell execution environments. **Smoosh** (`mgree/smoosh` @ `cc67dbe6a4953e51431997eac025b5e3f46c3d2d`, published at POPL 2020, DOI `10.1145/3371111`) provides the mechanized small-step operational model interpreting POSIX. **GNU Bash** (`mirror/bash` @ `b6e23235f28b1c85e18e9a2b7ba8c6b6c46aecbc`, tested at runtime `5.3.9(1)-release`) and **dash** (tested at runtime `0.5.12-12`) are examined as concrete production shell implementations compared against POSIX and Smoosh.
  - **GNU Make** (`mirror/make` @ `c63a5bc6a2881d515bb3020ed477fcba08fb2f3d`, tested at `4.4.1`), **CMake** (`Kitware/CMake` @ `2e0f6af547d479413b5553c635d14e9104ee04e4`), **GNU M4** (`autotools-mirror/m4` @ `e0e0f6eaccdb4ebdef4f7297fdffcbc3c8a4cdb8`, tested at `1.4.21`), and **GNU Autoconf M4sugar** (`autotools-mirror/autoconf` @ `a5dd14d6894e948bd1c312d11453f70a9dd7b47e`) are examined as a comparative family of phased string-expansion and build-graph languages.
  - **Tcl** (`tcltk/tcl` @ `f92685e14c135a586b1e4b842f373a4268c8417a`, Tcl 9 development tree) and **GNU Emacs Lisp** (`emacs-mirror/emacs` @ `dcdd799a863fc8c261e0628dede6da6dc64429d2`) are examined at the C runtime implementation level to characterize string-centric and dynamically scoped/advised execution models.
- **Version and environment constraints**:
  - POSIX.1-2024 (Issue 8) newly standardized `set -o pipefail` and `$'...'` dollar-single-quotes compared to POSIX.1-2017 (Issue 7). Smoosh (`cc67dbe6...`, 2020) targeted POSIX.1-2017; statements about `pipefail` reflect POSIX.1-2024 plus direct execution on `bash 5.3.9` and `dash 0.5.12-12`.
  - Tcl source inspection reflects the Tcl 9 `Tcl_Obj` layout (`Tcl_Size refCount`, `Tcl_Size length` replacing `int` in Tcl 8.6); the dual-port semantics and shimmering mechanism apply across both Tcl 8.6 and Tcl 9, while exact struct field widths are version-specific.
  - Runtime probes were executed on Linux x86-64 using `/usr/bin/dash` (`0.5.12-12`), `/usr/bin/bash` (`5.3.9(1)-release`), `/usr/bin/make` (`4.4.1`), and `/usr/bin/m4` (`1.4.21`). CMake, Tcl, and Emacs Lisp findings are grounded in direct source inspection without local binary execution (see `## Boundaries`).

## Findings

### 1. Cross-System Taxonomy of String-Rewriting and Phased-Execution Semantics

Basis: source + normative + derived

Although shells, build systems, macro processors, Tcl, and Emacs Lisp occupy different operational niches, static analysis and formal verification fail on all five for structurally related reasons: **late binding of syntax/values across evaluation phases** and **ambient mutable execution state**.

| System | Primary Representation | Evaluation / Expansion Phases | Quoting & Rescanning Discipline | Scoping / State Isolation Hazard | Principal Verification Obstacles |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **POSIX sh / Bash / Smoosh** | Byte strings + quote/field masks (`expanded_words` -> `intermediate_fields`) | Tokenize -> Parse -> 4-in-1 left-to-right expansion -> `$IFS` split -> Glob -> Quote removal -> Redirect -> Exec | Single expansion pass per command unless `eval`; double-quotes suppress splitting/globbing but not `$`/`` ` `` | Forked subshell environments copy state (mutations lost); dynamic `set -e` suppression (`CheckedExit`) | Dynamic `$IFS`, ambient filesystem globbing, non-local `set -e` suppression, async signal/trap interleaving |
| **GNU Make** | Unstructured character buffers (`struct variable`, `struct dep`) | Stage 1 (Read-in: `:=`, conditionals, targets, prereqs, `$(eval)`) -> Stage 2 (DAG update: `=`, `.SECONDEXPANSION`, recipes) | `$$` escapes `$` across one expansion pass; recipe lines undergo Make expansion then `/bin/sh` expansion | Global flat variable table + target-specific inheritance; `$(eval)` mutates Stage 1 graph mid-read | Two-language double escaping (Make + sh), dynamic prerequisite mutation via `$(eval)`, filesystem mtime races |
| **CMake** | `;`-delimited UTF-8 strings (`cmList`) + target property graphs | Stage 1 (Configure: `CMakeLists.txt` procedural script) -> Stage 2 (Generate: `$<...>` genex eval) -> Stage 3 (Backend build DAG) | `\"...\"` suppresses `;` list splitting on arguments; unquoted `${VAR}` splits on `;`; `\;` escapes list element | Directory/function variable scopes + global `CACHE` + target transitive `INTERFACE_*` properties | Semicolon injection in paths/flags, empty list element elision (`CMP0007`), unquoted `if()` dereference (`CMP0054`) |
| **GNU M4 / Autoconf** | Character input/output streams (`input_block` stack) | Single streaming loop with eager arg collection + output pushback rescanning; M4sugar overlays numbered diversions | Each macro expansion strips one `[...]` quote pair; output is rescanned until inert | Dynamic macro redefinition (`define`/`pushdef`/`popdef`); Autoconf `m4_require` reorders output via diversions | Quote-depth tracking errors (overquoting/underquoting), accidental active-token capture inside shell code |
| **Tcl** | Dual-ported `Tcl_Obj` (`bytes` UTF-8 string + cached `typePtr`/`internalRep`) | Single left-to-right 12-rule parse/substitute pass -> command dispatch (bytecode-compiled when static) | `{...}` defers all substitution; `"..."` allows `$`/`[...]`/`\`; `{*}` splices list elements before dispatch | Dynamic `uplevel`/`upvar` stack inspection; `trace` hooks on variable read/write/unset | Shimmering performance cliffs (`O(N)` re-parse), dynamic command renaming, `uplevel` aliasing caller frames |
| **GNU Emacs Lisp** | Tagged `Lisp_Object` + `Lisp_Symbol` (`redirect`, `declared_special`) | Reader -> Macroexpand -> Byte-compile / Interpret -> `funcall` / `specpdl` dynamic unwind | Traditional Lisp quoting (`'`, `` ` ``); `lexical-binding` is per-file header cookie, not global | `defvar` forces dynamic binding globally; `Lisp_Buffer_Local_Value` + `let` (`SPECPDL_LET_LOCAL` vs `DEFAULT`) | Global `advice-add` monkey-patching, buffer-switch interaction with `let`, byte-compiler inlining bypassing advice |

---

### 2. POSIX Shell Semantics and Smoosh Mechanization

#### 2.1 Smoosh Small-Step Operational Architecture

Basis: source (`mgree/smoosh` @ `cc67dbe6a4953e51431997eac025b5e3f46c3d2d`, `src/semantics.lem`, `src/os.lem`, `src/fields.lem`, `src/signal.lem`) + documentation (Greenberg & Blatt, POPL 2020, DOI `10.1145/3371111`)

Smoosh mechanizes POSIX shell semantics in Lem (extractable to OCaml and theorem provers) as a **small-step operational semantics** `step_eval : forall 'a. OS 'a => step_fun 'a` (`src/semantics.lem` L47). Critically, shell semantics cannot be isolated from the operating system because command substitution, pipelines, background jobs, redirections, `cd`, `umask`, and traps directly manipulate kernel state. Smoosh abstracts the OS via the `OS 'a` typeclass (`src/os.lem` L780–795), providing two concrete instantiations:

- **`os_system`** (`src/os_system.lem`): binds directly to POSIX syscalls (`fork`, `execve`, `pipe`, `waitpid`, `kill`, `dup2`) via OCaml shims (`src/shim.ml`) to serve as an executable reference shell.
- **`os_symbolic`** (`src/os_symbolic.lem`): models filesystem paths, file descriptors, processes, and symbolic strings purely functionally to power an interactive small-step stepper (`shtepper`) and symbolic exploration.

Every evaluation step passes through `check_traps` (`src/semantics.lem` L76), explicitly modeling asynchronous signal arrival and trap-action dispatch at POSIX command boundaries rather than hiding signals outside the semantics.

#### 2.2 Multi-Stage Word Expansion and `$IFS` Field Splitting

Basis: normative (POSIX.1-2024 §2.6, §2.6.5) + source (`mgree/smoosh` `src/semantics.lem` L517–587, `src/fields.lem` L20–40; `mirror/bash` `subst.c` L2286–2297, L9043–9054) + execution (`dash 0.5.12-12`, `bash 5.3.9`)

POSIX.1-2024 §2.6 mandates a strict four-phase expansion pipeline (subdivided into seven named operations):

```text
Stage 1 (left-to-right, single pass): Tilde (~) + Parameter ($var) + Command Subst ($(...)) + Arithmetic ($((...)))
   |  [produces expanded_words annotated with quoted/unquoted provenance]
   v
Stage 2: Field Splitting ($IFS) — ONLY on unquoted results from Stage 1 (ExpSplit)
   |  [produces intermediate_fields]
   v
Stage 3: Pathname Expansion (globbing *, ?, [...]) — skipped if `set -f` (ExpPath)
   |
   v
Stage 4: Quote Removal (\, ', ") — ALWAYS LAST (ExpQuote)
```

In Smoosh (`src/semantics.lem` L517–587), expansion is explicitly an explicit small-step state machine (`ExpStart opts w0` -> `ExpSplit opts f0` -> `ExpPath opts ...` -> `ExpQuote opts ...`), parameterized by context flags `opts = <| splitting = Split | NoSplit; globbing = bool |>`:
- Simple command words and `for` argument lists use `splitting = Split; globbing = true` (`L652`, `L1179`).
- Variable assignments (`x=w`) and `case` subject/pattern words use `splitting = NoSplit; globbing = false` (`L700`, `L1249`, `L1276`).
- Redirection targets use `splitting = NoSplit; globbing = is_interactive os0` (`L593`), matching POSIX's rule that non-interactive shells do not glob redirection pathnames.

**Critical `$IFS` Field-Splitting Rules (POSIX.1-2024 §2.6.5)**:
Let $W_{\text{IFS}} = \text{IFS} \cap \{\text{space}, \text{tab}, \text{newline}\}$ be *IFS white space* (`is_ws` in `smoosh/fields.lem` L32) and $D_{\text{IFS}} = \text{IFS} \setminus W_{\text{IFS}}$ be *IFS non-white-space* delimiters.
1. **Unset vs empty `IFS`**: If `IFS` is unset, it behaves identically to `IFS=$' \t\n'`. If `IFS=""` (set and empty), *no* field splitting occurs, **yet** any unquoted input field that expanded to the empty string is **deleted** before quote removal (whereas `""` is non-empty prior to quote removal and survives as a single empty field).
2. **Whitespace coalescing vs non-whitespace delimiters**: Leading and trailing sequences of $W_{\text{IFS}}$ are stripped. A single $d \in D_{\text{IFS}}$ together with any immediately adjacent $W_{\text{IFS}}$ forms **one** field delimiter. Consecutive $d_1, d_2 \in D_{\text{IFS}}$ (even separated by $W_{\text{IFS}}$) delimit an empty field between them.
3. **Trailing non-whitespace delimiter asymmetry**: A single trailing $d \in D_{\text{IFS}}$ terminates the final field and does **not** emit a trailing empty field, whereas a leading $d \in D_{\text{IFS}}$ **does** emit a leading empty field.

Verified directly on both `dash 0.5.12-12` and `bash 5.3.9(1)-release` (Probe B):
- `IFS=:; x="a::b:"; show $x` -> **3 fields**: `[a]`, `[]`, `[b]` (the trailing `:` does not yield a 4th empty field, while internal `::` yields `[]`).
- `IFS=" :"; x=" : a : : b : "; show $x` -> **4 fields**: `[]`, `[a]`, `[]`, `[b]` (leading space stripped, leading `:` produces `[]`, spaces around `:` merge with `:`, trailing `: ` produces no trailing empty field).
- `IFS=""; y=""; show $y "$y"` -> **1 field**: `[]` (unquoted empty `$y` is deleted; quoted `"$y"` survives).

In Bash (`subst.c` L9043–9054), `word_split(WORD_DESC *w, char *ifs_chars)` passes `xifs = ""` when `w->flags & W_QUOTED` is set, delegating the fine-grained quote-bit mask tracking to `list_string()`.

#### 2.3 `set -e` (`errexit`) Non-Compositional Suppression Pitfalls

Basis: normative (POSIX.1-2024 `set -e`) + source (`mgree/smoosh` `src/semantics.lem` L684, L764, L889, L930, L1026, L1388; `mirror/bash` `execute_cmd.c` L248–250, L565–566, L835–859) + execution (`dash 0.5.12-12`, `bash 5.3.9`)

`set -e` is **not** a lexically scoped exception mechanism; it is a dynamically inherited suppression context. Under POSIX.1-2024, `-e` is ignored throughout the evaluation of:
1. Any compound list following `if`, `elif`, `while`, or `until`;
2. Any pipeline beginning with `!`;
3. Any command of an AND-OR list (`&&`, `||`) other than the last;
4. Any individual command inside a multi-command pipeline (only the pipeline's overall status is checked).

**Mechanized representation**: Smoosh encodes this via a `checked_exit` context flag wrapped into AST nodes (`CheckedExit stmt'`). Whenever an error occurs, Smoosh exits iff `not (checked_exit checked) && Set.member Sh_errexit s.sh.opts` (`src/semantics.lem` L684, L764, L889, L930). Critically, at subshell entry (`src/semantics.lem` L1025–1038):
```ocaml
| Subshell stmt' (ers, Nothing, []) ->
   let checked_c = if checked_exit checked then CheckedExit stmt' else stmt' in
   ... fork_and_subshell s1 checked_c ...
```
Bash implements the analogous dynamic flag propagation by setting `CMD_IGNORE_RETURN` (`execute_cmd.c` L565–566, L855–856) on AST subtrees and gating `jump_to_top_level(ERREXIT)` on `ignore_return == 0 && invert == 0 && exit_immediately_on_error && pipe_in == NO_PIPE && pipe_out == NO_PIPE` (`execute_cmd.c` L843–850).

**Four concrete failure modes verified by execution (Probe A on `dash 0.5.12-12` and `bash 5.3.9`)**:

| Construct (under `set -e`) | Naive Expectation | Actual Observed Behavior (`dash` & `bash`) | Root Cause |
| :--- | :--- | :--- | :--- |
| `f() { false; echo AFTER; }; if f; then echo THEN; fi` | `f` aborts at `false`, enters `else` | Prints `AFTER` then `THEN` | `CheckedExit` / `CMD_IGNORE_RETURN` suppresses `-e` dynamically across the entire body of `f`; `echo AFTER` succeeds (`$?=0`), making `f` return `0` |
| `f() { false; echo AFTER; }; f \|\| true` | `f` aborts at `false` | Prints `AFTER` | LHS of `\|\|` dynamically disables `-e` for the entire call graph of `f` |
| `(false; echo IN_SUBSHELL) \|\| echo OUTER` | Subshell aborts at `false`, runs `OUTER` | Prints `IN_SUBSHELL` (does NOT run `OUTER`) | `CheckedExit` propagates across `fork_and_subshell` (`smoosh/semantics.lem` L1026), suppressing `-e` inside the subshell on the LHS of `\|\|` |
| `(false; echo ONE) \| cat; echo TWO` | Same as above or aborts script | Prints `TWO` only (`ONE` is NOT printed) | Inside a pipeline stage not under `CheckedExit`, the subshell DOES abort on `false`, while the outer pipeline exits `0` (`cat`), so `TWO` runs |
| `local x=$(false); echo SURVIVED:$?` vs `x=$(false)` | Both abort with rc=1 | `x=$(false)` aborts (`rc=1`); `local x=$(false)` prints `SURVIVED:0` | Standalone assignment inherits the command substitution's exit status; `local` is a builtin command whose own exit status is `0` after arguments finish expanding |

This asymmetry between `(false; echo IN_SUBSHELL) || echo OUTER` (prints `IN_SUBSHELL`) and `(false; echo ONE) | cat; echo TWO` (suppresses `ONE`) is a classic source of silent partial execution in error-handling wrappers. In particular, wrapping a helper function with `if helper; then ...` or `helper || handle_err` **silently disables every internal `set -e` guard inside `helper`** unless the caller executes the function in a fresh shell invocation or tests every command explicitly.

#### 2.4 Subshell Isolation, Pipelines, `pipefail`, and Signal/Trap Races

Basis: normative (POSIX.1-2024 §2.9.2, §2.13) + source (`mgree/smoosh` `src/semantics.lem` L924–940, `src/signal.lem` L16–79; `mirror/bash` `execute_cmd.c` L254–290, L2372) + execution (`dash 0.5.12-12`, `bash 5.3.9`)

- **Shell execution environment copying (POSIX.1-2024 §2.13)**: Subshells (`(...)`, command substitutions `$(...)`, asynchronous lists `cmd &`, and pipeline stages) inherit a *copy* of open file descriptors, `cwd`, `umask`, traps (caught traps reset to default for external scripts), variables, functions, and options. Mutations to variables, `cwd`, or traps inside a subshell **never propagate back** to the parent.
- **Pipeline last-stage ambiguity**: POSIX.1-2024 §2.13 allows *any or all* commands in a pipeline to execute in subshells. Consequently, `n=0; printf "a\nb\n" | while read -r line; do n=$((n+1)); done; echo $n` outputs `n=0` in both `dash 0.5.12-12` and default `bash 5.3.9` (because `while` runs in a forked subshell), whereas `bash +m -O lastpipe` (disabling job control `+m` and enabling `lastpipe_opt`, `execute_cmd.c` L289, L2372) runs the final stage in the current shell and outputs `n=2` (Probe C). (KornShell `ksh93` and `zsh` execute the final pipeline stage in the current shell by default; portable POSIX scripts must use process substitution, FIFOs, or redirections instead.)
- **Pipeline exit status & `pipefail`**: Prior to POSIX.1-2024, a pipeline's exit status was strictly the last command's status (`false | true` -> `0`). POSIX.1-2024 §2.9.2 standardized `set -o pipefail`: when enabled, the pipeline returns the rightmost non-zero exit status (or `0` if all succeed). Probe C confirms both `bash 5.3.9` and `dash 0.5.12-12` implement `set -o pipefail` (`false | true` returns `1`).
- **Pipeline wait & signal races**: POSIX.1-2024 §2.9.2 requires waiting for the last command and *permits* waiting for earlier stages. If an upstream producer writes to a pipe after a downstream consumer exits (e.g., `yes | head -n 1`), the kernel delivers `SIGPIPE` (`128 + 13 = 141` under Linux); with `set -o pipefail`, this benign early close causes the entire pipeline to fail with exit status `141`—a notorious interaction between `pipefail` and bounded-consumption pipelines. Furthermore, POSIX traps (`trap '...' INT`) are deferred while waiting on a foreground child until `waitpid` returns (the "wait and cooperative exit" / WCE vs immediate-exit model), creating race windows when a child catches and swallows `SIGINT` vs exits by `SIGINT`. Smoosh models signals explicitly via `type signal` and `signal_default_behavior` (`SigBeh_Terminate`, `SigBeh_Ignore`, `SigBeh_Stop`, `SigBeh_Continue` in `src/signal.lem` L16–79, L281–292), marking `SIGKILL` and `SIGSTOP` as `undefined_traps` (`L70–72`).

---

### 3. Build-Graph Languages and Two-/Three-Phase String Expansion

#### 3.1 GNU Make: Stage-1 Read-In vs Stage-2 DAG Evaluation

Basis: source (`mirror/make` @ `c63a5bc6a2881d515bb3020ed477fcba08fb2f3d`, `src/read.c` L132–154, L1898–1908, `src/expand.c` L145–156, `src/remake.c` L80–87, L119–130) + execution (`GNU Make 4.4.1`)

GNU Make is not a purely declarative DAG specification; it is a **two-phase string-rewriting engine driving a timestamped dependency graph**:

1. **Stage 1 — Read-In (`eval_makefile` -> `eval` -> `record_files`, `src/read.c` L132–148)**:
   Make reads makefiles top-to-bottom, building the internal hash table of `struct file` nodes and `struct dep` edges. During Stage 1, expansion is **immediate** for:
   - Left-hand sides of all variable assignments;
   - Right-hand sides of simply-expanded (`:=`, `::=`) and shell (`!=`) assignments;
   - Conditional directives (`ifeq`, `ifdef`);
   - Target lists and prerequisite lists of explicit and pattern rules (before `.SECONDEXPANSION:`);
   - Arguments to `$(eval ...)`, which recursively invoke `eval()` on dynamically synthesized Makefile syntax, mutating the DAG and variable table *mid-read*.
2. **Stage 2 — Goal Update & DAG Traversal (`update_goal_chain` -> `update_file_1` -> `remake_file`, `src/remake.c` L80–86, L119–130)**:
   Once all makefiles are read (and after re-execing itself if any included makefile was remade via `rebuilding_makefiles`, `src/remake.c` L124), Make traverses the dependency graph. Expansion is **deferred** until Stage 2 for:
   - Right-hand sides of recursively-expanded (`=`) variables (`recursively_expand_for_file`, `src/expand.c` L145);
   - Target-specific variables (`record_target_var`, `src/read.c` L149), which inherit down the prerequisite chain dynamically at execution time;
   - Second-expansion prerequisites enabled by `.SECONDEXPANSION:` (`second_expansion = 1`, `src/read.c` L1898–1900), where prerequisites undergo a *second* expansion pass after Stage 1 completes (requiring `$$` to protect variables from Stage 1);
   - Recipe lines, which expand via Make *immediately before spawning the shell* (each line in its own subshell unless `.ONESHELL:` is set, `src/read.c` L1905), followed by POSIX `/bin/sh` expansion of the resulting string.

**Empirical verification (Probe D on `GNU Make 4.4.1`)**:
Given:
```makefile
A = early
B := $(A)
C = $(A)
TARGET_DEP = dep1
all: $(TARGET_DEP)
	@echo "recipe: A=$(A) B=$(B) C=$(C) TARGET_DEP=$(TARGET_DEP) prereqs=$^"
A = late
TARGET_DEP = dep2
```
Make executed `dep1` and printed `recipe: A=late B=early C=late TARGET_DEP=dep2 prereqs=dep1`: the prerequisite list froze `TARGET_DEP=dep1` during Stage 1, even though `TARGET_DEP` resolved to `dep2` inside the Stage-2 recipe! Adding `.SECONDEXPANSION:` and writing `all: $(TARGET_DEP) $$(TARGET_DEP)` expanded the first token in Stage 1 (`dep1`) and the second in Stage 2 (`dep2`), running both targets (`prereqs=dep1 dep2`).

**Double-escaping hazard**: Because every recipe line passes sequentially through `expand.c` (`$`-expansion) and then `/bin/sh` (`$`-expansion, quoting, `$IFS`, globbing), shell variables must be written `$$var`, while Make automatic variables (`$@`, `$<`, `$^`) inject raw unescaped filenames directly into shell syntax—creating command-injection hazards whenever paths contain spaces, `$`, backticks, or `;`.

#### 3.2 CMake: Three-Stage Configure/Generate/Build Split and Semicolon Lists

Basis: source (`Kitware/CMake` @ `2e0f6af547d479413b5553c635d14e9104ee04e4`, `Source/cmList.h` L45–76, `Source/cmMakefile.cxx` L423–457, `Source/cmGeneratorExpression.h` L31–67)

CMake separates build specification into **three distinct semantic stages** with different data models and evaluation rules:

1. **Stage 1 — Configure Time (`cmMakefile`)**: An imperative string-typed language (`CMakeLists.txt`). Every variable value is a single UTF-8 string; lists are not first-class containers but `;`-delimited strings parsed on demand into `std::vector<std::string>` by `cmList` (`Source/cmList.h` L45–75), with explicit policy/API switches `EmptyElements::{No, Yes}` and `ExpandElements::{No, Yes}`.
   - Unquoted `${VAR}` arguments undergo `;`-splitting into multiple command arguments (with empty elements dropped by default unless preserved via `EmptyElements::Yes`), whereas quoted `"${VAR}"` passes a single string preserving `;` and empty elements.
   - Policy transitions historically altered fundamental syntax: `CMP0007` (retaining empty list elements in `list()`), `CMP0053` (simplified `@VAR@`/`${VAR}` expansion rules in `ExpandVariablesInString`), and `CMP0054` (preventing quoted `"FOO"` inside `if("FOO" STREQUAL ...)` from implicitly dereferencing a variable named `FOO`!).
2. **Stage 2 — Generate Time (`cmGeneratorExpression`, `Source/cmGeneratorExpression.h` L31–67)**: Multi-configuration generators (Visual Studio, Xcode, Ninja Multi-Config) do not know the build configuration (`Debug`/`Release`) during Configure Time. CMake therefore embeds a **second pure functional string-rewriting DSL** (`$<CONFIG:Debug>`, `$<TARGET_PROPERTY:...>`, `$<COMPILE_LANGUAGE:C>`) inside target properties. `cmGeneratorExpression::Evaluate(...)` (`L54–59`) resolves these strings *after* all `CMakeLists.txt` files finish configuring, guarded by a `cmGeneratorExpressionDAGChecker` to detect cyclic target-property dependencies. Some properties explicitly ban Stage-2 expressions via `ForbidGeneratorExpressions` (`L61–67`).
3. **Stage 3 — Build Time**: The emitted Ninja/Make/MSBuild files execute the static DAG. Changing build inputs that affect Stage 1 requires re-running `cmake` (detected via CMake's own regeneration rules); runtime-generated header dependencies are handled outside Stage 1 via compiler depfiles (`-MD`/`-MF`) or C++20 module dyndep scanning.

#### 3.3 GNU M4 and Autoconf M4sugar: Rescanning Streams and Diversion Scheduling

Basis: source (`autotools-mirror/m4` @ `e0e0f6eaccdb4ebdef4f7297fdffcbc3c8a4cdb8`, `src/macro.c` L27–40, L142–155, L281–284, `src/input.c` L48–62, L446–455; `autotools-mirror/autoconf` @ `a5dd14d6894e948bd1c312d11453f70a9dd7b47e`, `lib/m4sugar/m4sugar.m4` L867–881, L1467–1482) + execution (`GNU M4 1.4.21`)

GNU M4 is a **stream-based macro processor** with no AST and no separation between code and data:

1. **Eager argument expansion + input-stack rescanning**: In `src/macro.c`, when `expand_macro` recognizes an active symbol, `expand_argument` (`L142–155`) consumes arguments by recursively expanding tokens until balanced `,` or `)` at `paren_level == 0`—meaning **unquoted arguments are evaluated eagerly before the macro body runs**. `call_macro` (`L281–284`) then writes the expanded text into an obstack and pushes it onto the front of the input stack (`push_string_init`/`push_string_finish` in `src/input.c` L48–52), so the lexer (`next_token`) **immediately rescans the macro output as fresh input**.
2. **One quote layer stripped per scan**: Each time a quoted string (`[...]` under Autoconf's `changequote([, ])`) is scanned, the outermost quote pair is removed and its interior is emitted verbatim *without* scanning. Consequently, passing a macro through $k$ intermediate forwarding macros strips $k$ layers of quoting unless re-quoted.

**Empirical verification (Probe E on `GNU M4 1.4.21`)**:
With `changequote([, ])`, `define([A], [B])`, `define([B], [EXPANDED_B])`, and `define([WRAP], [$1])`:
- `A` -> `EXPANDED_B` (rescanned twice: `A` -> `B` -> `EXPANDED_B`);
- `[A]` -> `A` (1 quote layer stripped, no rescan);
- `[[A]]` -> `[A]` (1 quote layer stripped);
- `WRAP([A])` -> `EXPANDED_B` (1 layer stripped during argument collection giving `$1 = A`, then `WRAP` emits `A` onto the input stack, which rescans to `EXPANDED_B`!);
- `WRAP([[A]])` -> `A` (1 layer stripped on arg collection -> `[A]`, 2nd layer stripped on rescan -> `A`);
- `define([EAGER], A)EAGER` -> `EXPANDED_B` (`A` expanded eagerly during `define`'s argument collection before `EAGER` was defined!).

3. **Autoconf M4sugar workarounds**: Because Autoconf generates POSIX shell scripts (`configure`) containing shell constructs with unmatched `)` (such as `case $x in foo) ... ;; esac`) and brackets `[...]`, M4sugar (`lib/m4sugar/m4sugar.m4` L867–881) must use temporary `m4_changequote` hacks and sentinel markers to detect underquoted `)` in `m4_expand`. Furthermore, to impose dependency ordering on text macros without a build-graph engine, `m4_defun` and `m4_require` (`m4sugar.m4` L1467–1482) allocate **decreasing numbered M4 diversions** (`GROW`, `GROW - 1`, `GROW - 2`, ...): when `TEST1` invokes `m4_require([TEST2])` which invokes `m4_require([TEST3])`, each dependency writes its shell initialization code into a lower-numbered diversion, and `TEST1`'s epilogue undiverts `GROW - 2`, `GROW - 1`, `GROW` in ascending order so prerequisites precede dependents in the emitted `configure` script.

---

### 4. Tcl Everything-Is-A-String (EIAS) and `Tcl_Obj` Shimmering

#### 4.1 The 12-Rule Syntax (*Dodekalogue*)

Basis: normative/documentation (`tcltk/tcl` @ `f92685e14c135a586b1e4b842f373a4268c8417a`, `doc/Tcl.n` L20–275)

Unlike POSIX shell (which performs multi-stage splitting and globbing *after* substitution), Tcl's grammar is defined by **exactly twelve rules** (`doc/Tcl.n` L20–265):
1. `[1] Commands` — newline/semicolon-separated sequences of words.
2. `[2] Evaluation` — single pass producing word values; word 0 is looked up as a command procedure and invoked with remaining words.
3. `[3] Words` — whitespace-separated tokens.
4. `[4] Double quotes` — `"..."` groups whitespace into one word while allowing rules `[7]`, `[8]`, `[9]`.
5. `[5] Argument expansion` — `{*}word` (introduced in Tcl 8.5) parses the substituted word as a Tcl list and splices its elements as separate command arguments prior to dispatch.
6. `[6] Braces` — `{...}` defers *all* substitutions (preserving balanced nested braces verbatim; only `\<newline>` is collapsed), acting as the canonical quoting mechanism for code blocks (`if`, `while`, `proc`) and expressions (`expr`).
7. `[7] Command substitution` — `[script]` recursively evaluates `script` and substitutes its result.
8. `[8] Variable substitution` — `$name`, `$name(index)`, `${name}`.
9. `[9] Backslash substitution` — escape sequences (`\n`, `\xhh`, `\uhhhh`, `\Uhhhhhhhh`, `\<newline>`).
10. `[10] Comments` — `#` is a comment **only** where a command name is expected (Rule `[10]`), explaining why `#` inside a braced `if` body or after a command requires a preceding `;` (`set x 1 ;# comment`) and why unbalanced `{` inside a `#` comment inside a braced block still breaks Rule `[6]` brace matching!
11. `[11] Order of substitution` — strictly left-to-right, **single pass**: characters produced by `[7]`/`[8]`/`[9]` are **never rescanned** for further substitutions.
12. `[12] Substitution and word boundaries` — substitutions do not affect word boundaries (unlike shell `$IFS` splitting), except explicitly under Rule `[5]` `{*}`.

Because of Rule `[11]` and `[12]`, `set x "a b"; cmd $x` passes **one** argument `"a b"` cleanly without shell-style word-splitting bugs; conversely, omitting braces around `expr` (`expr $a + $b` instead of `expr {$a + $b}`) causes double substitution (first by Tcl's parser, then by `expr`'s parser), creating both a code-injection vulnerability and a bytecode-compilation deoptimization.

#### 4.2 Dual-Ported `Tcl_Obj` and Shimmering Mechanics

Basis: source (`tcltk/tcl` @ `f92685e14c135a586b1e4b842f373a4268c8417a`, `generic/tcl.h` L635–650, L690–737; `generic/tclObj.c` L923–966, L1378)

Semantically, every Tcl value is an immutable string (with copy-on-write mutation via reference counting `refCount`). To avoid $O(N)$ string reparsing on every integer addition, list index, or dictionary lookup, Tcl 8.0+ represents every value as a **dual-ported `Tcl_Obj`** (`generic/tcl.h` L716–737):

```c
typedef struct Tcl_Obj {
    Tcl_Size refCount;            /* CoW sharing & lifetime counter */
    char *bytes;                  /* UTF-8 string rep (NULL => invalid/lazy) */
    Tcl_Size length;              /* Byte length excluding trailing NUL */
    const Tcl_ObjType *typePtr;   /* Current cached internal rep type (or NULL) */
    Tcl_ObjInternalRep internalRep; /* Tagged union: long/double/wide/twoPtr/ptrAndLong */
} Tcl_Obj;
```

Each `Tcl_ObjType` (`generic/tcl.h` L635–650) defines four hooks: `freeIntRepProc`, `dupIntRepProc`, `updateStringProc` (lazily materializes `bytes` from `internalRep`), and `setFromAnyProc` (parses `bytes` into `internalRep`, freeing any prior `internalRep`).

**The dual-port state machine**:
- **Pure string**: `bytes != NULL`, `typePtr == NULL`.
- **Pure internal rep**: `bytes == NULL`, `typePtr != NULL` (e.g., an integer result of `expr` or a freshly constructed list whose string rep has never been requested).
- **Dual-ported**: `bytes != NULL`, `typePtr != NULL` (both representations are cached and semantically coherent).
- **Mutation**: Modifying an unshared `Tcl_Obj` (`refCount <= 1`) updates `internalRep` and calls `Tcl_InvalidateStringRep`, setting `bytes = NULL`; modifying a shared `Tcl_Obj` (`refCount > 1`) triggers copy-on-write duplication first.

**Shimmering pathology**: Whenever a command requires type $T_2$ on an object currently carrying `typePtr == T_1` ($T_1 \neq T_2$), `Tcl_ConvertToType` (`generic/tclObj.c` L941–966) invokes `T_2->setFromAnyProc(interp, objPtr)`, which first ensures `bytes != NULL` (calling `T_1->updateStringProc` if needed), then invokes `T_1->freeIntRepProc` and re-parses `bytes` into `T_2`. Note that `Tcl_Obj` holds **only one `internalRep` slot**! Therefore, alternating two incompatible views on the same value inside a loop—for example:
1. Treating a list object alternately with `string length` (converting to UTF-8 string internal rep) and `lindex` (converting back to `list` rep), or
2. Passing a `dict` to `lindex`/`llength` (shimmering between hash-table `dict` rep and array `list` rep), or
3. Evaluating an unbraced script/expression string (shimmering between `bytecode` rep and `string`/`list` rep)—
causes **continuous representation thrashing (shimmering)**: each iteration pays $O(N)$ serialization and/or parsing, turning an apparently $O(N)$ loop into $O(N^2)$ and breaking pointer/bytecode caches. Crucially, under EIAS, shimmering must remain **observationally invisible** in result values (except timing and canonical formatting edge cases where `updateStringProc` only fires after `bytes` is invalidated).

---

### 5. GNU Emacs Lisp: Dynamic vs Lexical Scope, Buffer-Local Variables, and Advice

#### 5.1 Symbol Redirection, `declared_special`, and `specpdl`

Basis: source (`emacs-mirror/emacs` @ `dcdd799a863fc8c261e0628dede6da6dc64429d2`, `src/lisp.h` L784–837, L3100–3121; `src/eval.c` L3667–3709; `src/data.c` L1626–1641)

Emacs Lisp is a Lisp-2 (separate `val` and `function` slots on `struct Lisp_Symbol`, `src/lisp.h` L799–836) that historically supported only dynamic binding until file-local lexical binding (`-*- lexical-binding: t -*-`) was added in Emacs 24. Even when `lexical-binding` is enabled, **dynamic binding remains active for every symbol whose `declared_special` bit is `1`** (`src/lisp.h` L817), set globally by `defvar`, `defcustom`, or `defconst`.

Every `struct Lisp_Symbol` stores a 2-bit `redirect` field (`enum symbol_redirect`, `src/lisp.h` L784–790):
- `SYMBOL_PLAINVAL`: ordinary global value stored directly in `sym->u.s.val.value`.
- `SYMBOL_VARALIAS`: forwards recursively to another `struct Lisp_Symbol *alias` (`src/data.c` L1636).
- `SYMBOL_LOCALIZED`: points to a `struct Lisp_Buffer_Local_Value *blv` (`src/lisp.h` L3100–3121) implementing per-buffer dynamic state.
- `SYMBOL_FORWARDED`: points to a C-level `lispfwd` descriptor (`DEFVAR_INT`, `DEFVAR_BOOL`, per-buffer C struct slots `BUFFER_OBJFWDP`, or per-kboard slots).

Dynamic bindings (`let` / `let*` on special variables or under dynamic binding) push unwind records onto the C **special-binding stack `specpdl`** via `specbind()` (`src/eval.c` L3667–3709) and restore prior values via `unbind_to()` on normal return or non-local exit (`throw`, `signal`/error).

#### 5.2 Buffer-Local Variable Cache and `let` Interaction Anomalies

Basis: source (`emacs-mirror/emacs` @ `dcdd799a863fc8c261e0628dede6da6dc64429d2`, `src/lisp.h` L3100–3121; `src/eval.c` L3685–3709; `src/data.c` L1638–1641, L2187–2269)

A `SYMBOL_LOCALIZED` variable uses `struct Lisp_Buffer_Local_Value` (`src/lisp.h` L3100–3121) as a **single-entry cache** over per-buffer alists:
- `local_if_set` (`1` for `make-variable-buffer-local`, `0` for one-buffer `make-local-variable`): controls whether `setq` creates a new buffer-local entry automatically.
- `where`: the buffer for which `valcell` is currently swapped in.
- `defcell`: `(SYMBOL . DEFAULT-VALUE)` shared by all buffers without a local binding.
- `valcell`: `(SYMBOL . VALUE)` from `where`'s local variable alist, or `eq` to `defcell` if `where` has no local binding (`found == 0`).

On every read (`find_symbol_value`, `src/data.c` L1638–1641), Emacs calls `swap_in_symval_forwarding(sym, blv)` to synchronize `blv->where` with `current_buffer`. This architecture produces **two major semantic traps** directly encoded in `specbind()` (`src/eval.c` L3685–3709):

1. **`let` binds the *default* cell when no local binding exists (`SPECPDL_LET_DEFAULT`)**:
   In `specbind` (`src/eval.c` L3697–3701):
   ```c
   if (sym->u.s.redirect == SYMBOL_LOCALIZED) {
       if (!blv_found (SYMBOL_BLV (sym)))
           specpdl_ptr->let.kind = SPECPDL_LET_DEFAULT;
   }
   ```
   If `v` was declared with `(make-variable-buffer-local 'v)` (`local_if_set = 1`) and buffer $B_1$ has *not* yet set `v` locally, `(let ((v 1)) ...)` records `SPECPDL_LET_DEFAULT` and overwrites `defcell`! As a result:
   - Every *other* buffer without its own local binding temporarily observes `v = 1` during the dynamic extent of the `let`;
   - Calling `(setq v 2)` *inside* that `let` does **not** make `v` local to $B_1$ (explicitly documented in `Fmake_variable_buffer_local`, `src/data.c` L2193–2195), and the assignment is discarded when `let` unwinds!
2. **`let` on an existing local binding is pinned to the entry buffer (`SPECPDL_LET_LOCAL`)**:
   When `blv_found(blv)` is true in buffer $B_1$, `specbind` records `SPECPDL_LET_LOCAL` with `specpdl_ptr->let.where.buf = Fcurrent_buffer()` (`src/eval.c` L3689–3692). If the body executes `(with-current-buffer B2 ...)`:
   - Inside $B_2$, `v` resolves to $B_2$'s own value (or default), **not** the `let`-bound value from $B_1$;
   - If the body switches permanently to $B_2$ via `set-buffer` without restoring $B_1$ before exiting the `let`, `unbind_to` restores $B_1$'s saved value cleanly (fixing an ancient pre-Emacs-24 leak where `unbind_to` restored into the wrong buffer), yet any intermediate mutation in $B_2$ was never scoped by the `let`.

#### 5.3 Function Advice (`nadvice.el`) and Compilation/Inlining Bypass

Basis: source (`emacs-mirror/emacs` @ `dcdd799a863fc8c261e0628dede6da6dc64429d2`, `lisp/emacs-lisp/nadvice.el` L66–81, L509–525)

Emacs Lisp's `nadvice.el` provides runtime aspect-oriented monkey-patching of any named function, macro, or alias via `(advice-add SYMBOL HOW FUNCTION &optional PROPS)` (`nadvice.el` L509). The combinator algebra (`advice--how-alist`, `nadvice.el` L66–78) composes a new advice function `car` with the existing function `cdr` over argument list `r` using eleven combinators:
- `:around` -> `(apply car cdr r)` (full interception / argument & return rewriting / short-circuiting)
- `:before` -> `(apply car r) (apply cdr r)`
- `:after` -> `(prog1 (apply cdr r) (apply car r))`
- `:override` -> `(apply car r)` (replaces underlying implementation completely)
- `:filter-args` -> `(apply cdr (funcall car r))`
- `:filter-return` -> `(funcall car (apply cdr r))`
- `:before-while` / `:before-until` / `:after-while` / `:after-until` -> short-circuiting `and`/`or` compositions
- `:interactive-only` -> metadata-only wrapper `(apply cdr r)`

**Semantic and static-analysis hazards**:
1. **Unrestricted global mutability of function cells**: `advice-add` replaces `(symbol-function symbol)` in-place (`fset`, `nadvice.el` L519), breaking any closed-world assumption about callee behavior, purity, or invariants.
2. **Asymmetric observability across compilation tiers**: Because `nadvice.el` operates solely on the symbol's `function` slot:
   - Calls compiled into dedicated **byte-code opcodes** (e.g., `car`, `cdr`, `cons`, `+`, `eq`, `point`, `goto-char`) bypass `symbol-function` dispatch unless byte-compilation opted out;
   - Functions defined with `defsubst` (inlined at compile time) or expanded via `define-compiler-macro` or `defmacro` into already-compiled `.elc` or native-compiled (`.eln`) callers **never see advice added after compilation**;
   - C primitives calling other C primitives directly via C function pointers (`F...(...)`) bypass Lisp-level advice on the callee symbol entirely.

## Boundaries

- **CMake, Tcl, and Emacs Lisp runtime execution (`not examined`)**: `cmake`, `tclsh`, and `emacs` binaries were not installed in the local probe environment; findings for CMake (`cmList`, `cmGeneratorExpression`), Tcl (`Tcl_Obj`, `Tcl.n`), and Emacs Lisp (`Lisp_Symbol`, `specbind`, `nadvice.el`) are established by direct source inspection at pinned upstream commits rather than local execution probes.
- **POSIX.1-2024 vs historical POSIX.1-2017 implementations (`known not to apply`)**: `set -o pipefail` is normative in POSIX.1-2024 (Issue 8) and verified present in `dash 0.5.12-12` and `bash 5.3.9`, but is **known not to apply** to older POSIX.1-2017 shells (e.g., `dash <= 0.5.11` or minimal BusyBox ash builds compiled without `ASH_BASH_COMPAT`). Similarly, Smoosh (`cc67dbe6...`) formalized POSIX.1-2017 and does not include POSIX.1-2024's `$'...'` or `pipefail`.
- **Non-POSIX shell extensions (`not examined`)**: `zsh` (which disables `$IFS` splitting on unquoted parameter expansions by default unless `SH_WORD_SPLIT` is set), `fish`, `Oil`/`YSH`, `ksh93`, and `Ninja`/`Bazel` Starlark (which deliberately eliminate Turing-complete string expansion in favor of hermetic typed graphs) were not directly inspected in this report.
- **Tcl 8.6 vs Tcl 9 C-ABI layout (`known not to apply`)**: The `Tcl_Obj` struct quoted from `tcltk/tcl` @ `f92685e14c...` uses `Tcl_Size` (`ptrdiff_t`) for `refCount` and `length` (Tcl 9 ABI). On Tcl 8.6, those fields are `int`; the dual-port shimmering mechanism is shared, but binary struct offsets do not transfer across major versions.
- **Emacs native compilation (`comp.c` / `libgccjit`) interaction with advice (`unknown` / `not examined`)**: Whether specific `native-comp-speed` optimization levels inline non-`defsubst` sibling calls within a compilation unit in ways that further bypass `nadvice.el` was not verified by execution or `src/comp.c` inspection.
- **Stronger conclusion NOT established**: Passing Smoosh's POSIX conformance suite or enabling `set -euo pipefail` does **not** make a shell script fail-fast or injection-safe; as Probe A demonstrates, `set -e` is silently defeated by `if fn`, `fn || ...`, `local x=$(false)`, and subshells inside AND-OR lists, while `pipefail` introduces false-positive `SIGPIPE` (`141`) aborts in short-circuiting pipelines.

## Evidence

### Normative Specifications and Peer-Reviewed Sources
1. **IEEE Std 1003.1-2024 (POSIX.1-2024 / The Open Group Base Specifications Issue 8)**, Chapter 2 *Shell Command Language* (`https://pubs.opengroup.org/onlinepubs/9799919799/utilities/V3_chap02.html`, retrieved 2026-11-19):
   - §2.6 *Word Expansions*: four-stage expansion ordering (tilde/parameter/command-subst/arithmetic -> field splitting -> pathname expansion -> quote removal).
   - §2.6.5 *Field Splitting*: `IFS` unset vs empty removal rule, `IFS` white-space coalescing, non-white-space delimiter splitting.
   - §2.9.2 *Pipelines*: pipeline I/O connection prior to redirections, foreground wait semantics, normative `pipefail` exit-status table.
   - §2.13 *Shell Execution Environment*: components copied into subshells and separate utility environments.
   - `set -e` specification: explicit enumeration of suppression contexts (`if`/`elif`/`while`/`until`, `!`, non-final AND-OR commands, multi-command pipeline stages) and subshell examples.
2. **Michael Greenberg and Austin J. Blatt**, *"Executable Formal Semantics for the POSIX Shell (Smoosh: the Symbolic, Mechanized, Observable, Operational Shell)"*, *Proc. ACM Program. Lang.* (PACMPL), Vol. 4, POPL 2020, Article 43, Jan 2020, DOI `10.1145/3371111`.

### Pinned Upstream Source Inspections (Observed 2026-11-19)
- **`mgree/smoosh` @ `cc67dbe6a4953e51431997eac025b5e3f46c3d2d`**:
  - `src/semantics.lem`: `step_eval` (L47), `check_traps` (L76), `ExpStart`/`ExpSplit`/`ExpPath`/`ExpQuote` (L517–587), redirection expansion options `splitting = NoSplit; globbing = is_interactive os0` (L589–599), `CheckedExit` + `Sh_errexit` checks (L684, L764, L889, L930, L1388, L1476), `Pipe` (L924–940), `Subshell` `CheckedExit` propagation (L1025–1038).
  - `src/fields.lem`: `is_ws` (`" \n\t"`, L32), `collect_non_ifs`, `split_fields`, `field_splitting` (L20–40).
  - `src/os.lem`: `update_trap` (L624–630), `os_fork_and_subshell` / `os_waitpid` abstract `OS` methods (L782–793).
  - `src/signal.lem`: `type signal` (L16–28), `undefined_traps = [SIGKILL; SIGSTOP]` (L70–72), `signal_default_behavior` (L281–292).
- **`mirror/bash` @ `b6e23235f28b1c85e18e9a2b7ba8c6b6c46aecbc`**:
  - `execute_cmd.c`: `comsub_ignore_return`, `subshell_environment`, `lastpipe_opt` (L248–290, L2372), `CMD_IGNORE_RETURN` propagation under `exit_immediately_on_error` (L565–566, L835–859).
  - `subst.c`: `string_list_dollar_at` (L2286–2297), `word_split` (L9043–9054).
- **`mirror/make` @ `c63a5bc6a2881d515bb3020ed477fcba08fb2f3d`**:
  - `src/read.c`: `eval_makefile`, `eval`, `record_files`, `record_target_var` (L132–154), `.SECONDEXPANSION` and `.ONESHELL` flags (L1898–1908).
  - `src/expand.c`: `recursively_expand_for_file` (L145–156).
  - `src/remake.c`: `update_file_1`, `remake_file` (L80–86), `update_goal_chain` & `rebuilding_makefiles` (L119–130).
- **`Kitware/CMake` @ `2e0f6af547d479413b5553c635d14e9104ee04e4`**:
  - `Source/cmList.h`: `class cmList`, `EmptyElements`, `ExpandElements` (L45–76).
  - `Source/cmMakefile.cxx`: `ExpandVariablesInString` invocation during command argument trace/evaluation (L423–428).
  - `Source/cmGeneratorExpression.h`: `class cmGeneratorExpression`, `Evaluate`, `ForbidGeneratorExpressions` (L31–67).
- **`autotools-mirror/m4` @ `e0e0f6eaccdb4ebdef4f7297fdffcbc3c8a4cdb8`**:
  - `src/macro.c`: `expand_macro`, `expansion_level` (L27–40), `expand_argument` (L142–155), `call_macro` (L281–284).
  - `src/input.c`: `push_string_init`/`push_string_finish` input-stack rescanning (L48–62), `init_macro_token` (L446–455).
- **`autotools-mirror/autoconf` @ `a5dd14d6894e948bd1c312d11453f70a9dd7b47e`**:
  - `lib/m4sugar/m4sugar.m4`: `m4_expand` quoting/unbalanced-`)` sentinel mechanism (L867–881), `m4_defun`/`m4_require` `GROW - k` diversion ordering (L1467–1482).
- **`tcltk/tcl` @ `f92685e14c135a586b1e4b842f373a4268c8417a`**:
  - `doc/Tcl.n`: 12 syntactic rules `[1]`–`[12]` (L20–275).
  - `generic/tcl.h`: `struct Tcl_ObjType` (L635–650), `union Tcl_ObjInternalRep` (L690–705), `struct Tcl_Obj` (L716–737).
  - `generic/tclObj.c`: `Tcl_ConvertToType` (L941–966), `TclFreeInternalRep` (L1378).
- **`emacs-mirror/emacs` @ `dcdd799a863fc8c261e0628dede6da6dc64429d2`**:
  - `src/lisp.h`: `enum symbol_redirect` (L784–790), `struct Lisp_Symbol` with `declared_special` (L799–837), `struct Lisp_Buffer_Local_Value` (L3100–3121).
  - `src/eval.c`: `specbind` (`SPECPDL_LET`, `SPECPDL_LET_LOCAL`, `SPECPDL_LET_DEFAULT`, L3667–3709).
  - `src/data.c`: `find_symbol_value` (L1626–1641), `Fmake_variable_buffer_local` (L2187–2202), `Fmake_local_variable` (L2254–2269).
  - `lisp/emacs-lisp/nadvice.el`: `advice--how-alist` (L66–78), `advice-add` (L509–525).

### Local Execution Probes (Observed 2026-11-19, Linux x86-64)
Executed with `/usr/bin/dash` (`0.5.12-12`), `/usr/bin/bash` (`5.3.9(1)-release`), `/usr/bin/make` (`GNU Make 4.4.1`), and `/usr/bin/m4` (`GNU M4 1.4.21`):

```sh
# Probe A: set -e suppression (identical output on dash 0.5.12-12 and bash 5.3.9)
sh -c 'set -e; f() { false; echo "AFTER_FALSE"; }; if f; then echo "THEN"; else echo "ELSE"; fi'
# -> AFTER_FALSE\nTHEN
sh -c 'set -e; (false; echo "IN_SUBSHELL") || echo "OUTER_OR"'
# -> IN_SUBSHELL
sh -c 'set -e; (false; echo "ONE") | cat; echo "TWO"'
# -> TWO
sh -c 'set -e; f() { local x=$(false); echo "SURVIVED_LOCAL:$?"; }; f'
# -> SURVIVED_LOCAL:0
sh -c 'set -e; x=$(false); echo "SURVIVED_ASSIGN:$?"'
# -> (exits immediately with status 1)

# Probe B: IFS splitting (identical output on dash 0.5.12-12 and bash 5.3.9)
sh -c 'show() { printf "argc=%d:" "$#"; for a in "$@"; do printf " [%s]" "$a"; done; echo; };
  IFS=:; x="a::b:"; show $x;
  IFS=" :"; x=" : a : : b : "; show $x;
  IFS=""; y=""; show $y "$y"'
# -> argc=3: [a] [] [b]
# -> argc=4: [] [a] [] [b]
# -> argc=1: []

# Probe C: Pipeline subshell state loss & pipefail
dash -c 'n=0; printf "a\nb\n" | while read -r l; do n=$((n+1)); done; echo "n=$n"'       # -> n=0
bash -c 'n=0; printf "a\nb\n" | while read -r l; do n=$((n+1)); done; echo "n=$n"'       # -> n=0
bash +m -O lastpipe -c 'n=0; printf "a\nb\n" | while read -r l; do n=$((n+1)); done; echo "n=$n"' # -> n=2
dash -c 'set -o pipefail; false | true; echo "rc=$?"'                                     # -> rc=1
bash -c 'false | true; echo -n "off=$? "; set -o pipefail; false | true; echo "on=$?"'   # -> off=0 on=1

# Probe D: GNU Make 4.4.1 two-stage expansion vs .SECONDEXPANSION
# Makefile (see Findings §3.1): all: $(TARGET_DEP) with TARGET_DEP redefined after rule
# -> ran dep1; recipe: A=late B=early C=late TARGET_DEP=dep2 prereqs=dep1
# Makefile.second (.SECONDEXPANSION: all: $(TARGET_DEP) $$(TARGET_DEP))
# -> ran dep1; ran dep2; secondexp prereqs=dep1 dep2

# Probe E: GNU M4 1.4.21 rescanning & quote depth
m4 <<'EOF'
changequote(`[', `]')dnl
define([A], [B])dnl
define([B], [EXPANDED_B])dnl
define([WRAP], [$1])dnl
1: A | 2: [A] | 3: [[A]] | 4: WRAP([A]) | 5: WRAP([[A]]) | 6: define([EAGER], A)EAGER
EOF
# -> 1: EXPANDED_B | 2: A | 3: [A] | 4: EXPANDED_B | 5: A | 6: EXPANDED_B
```

## Revalidation

Each major claim can be cheaply revalidated on another shell, build tool, or upstream commit using narrow discriminating probes:

1. **Shell `set -e`, `$IFS`, and `pipefail` conformance**: Run Probes A–C above under any target `/bin/sh` implementation (`ash`, `mksh`, `yash`, `zsh --emulate sh`, `ksh93`, or newer `dash`/`bash`). Divergences immediately expose non-POSIX `CheckedExit` propagation into subshells, `IFS` trailing-delimiter bugs, `lastpipe` defaults, or missing POSIX.1-2024 `pipefail` support.
2. **GNU Make two-phase & `.SECONDEXPANSION` semantics**: Run the 10-line `Makefile` and `Makefile.second` from Probe D under the target `make` binary (e.g., BSD `bmake` vs GNU Make 4.4+) to verify Stage-1 prerequisite freezing vs Stage-2 recipe and secondary expansion.
3. **CMake policy & generator-expression boundary**: Diff `Source/cmList.h` (`EmptyElements`), `Source/cmGeneratorExpression.h` (`Evaluate`, `ForbidGeneratorExpressions`), and policy defaults (`CMP0007`, `CMP0053`, `CMP0054`) against the pinned `Kitware/CMake` commit, or execute a minimal `CMakeLists.txt` with `cmake -P` testing `set(L "a;;b")` and `if("VAR" STREQUAL ...)`.
4. **Tcl shimmering regression check**: On a host with `tclsh`, inspect internal representation transitions directly via `::tcl::unsupported::representation $obj` across alternating `llength` / `string length` / `dict size` calls on a shared variable.
5. **Emacs Lisp buffer-local `let` and advice bypass check**: On a host with `emacs --batch`, evaluate `(let ((v 1)) ...)` over a `make-variable-buffer-local` symbol with and without an existing local binding across `(with-current-buffer ...)` and check `(byte-compile (lambda () (defsubst-fn)))` before and after `(advice-add 'defsubst-fn :override ...)`.
