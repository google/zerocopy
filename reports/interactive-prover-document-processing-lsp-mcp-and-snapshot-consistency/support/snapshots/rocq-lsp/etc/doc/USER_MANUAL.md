# `rocq-lsp` user manual

Welcome to `rocq-lsp` in-progress user-manual.

Please see also `rocq-lsp` FAQ.

## First steps with `rocq-lsp`

`rocq-lsp` is designed to work on a project-basis, that is to say, the
user should point to the _root_ of their project (for example using
"Open Folder" in VSCode).

Given a project root `dir`, `rocq-lsp` will try to read
`$dir/_RocqProject` (or `$dir/_CoqProject` if the first is not
detected) and will apply the settings for your project from there.

Other tools included in the `rocq-lsp` suite usually take a
`--root=dir` command line parameter to set this information up.

`rocq-lsp` will display information about the project root and setting
auto-detection using the standard language server protocol messaging
facilities. In VSCode, these settings can be usually displayed in the
"Output > rocq-lsp server" window.

## Key features:

### Continuous vs on-demand mode

`rocq-lsp` offers two checking modes:

- continuous checking [default]: `rocq-lsp` will check all your open
  documents eagerly. This is best when working with powerful machines
  to minimize latency. When using OCaml 4.x, `rocq-lsp` uses the
  `memprof-limits` library to interrupt Rocq and stay responsive.

- on-demand checking [set the `check_only_on_request` option]: In this
  mode, `rocq-lsp` will stay idle and only compute information that is
  demanded, for example, when the user asks for goals. This mode
  disables some useful features such as `documentSymbol` as they can
  only be implemented by checking the full file.

  This mode can use the `check_on_scroll` option, which improves
  latency by telling `rocq-lsp` to check eagerly what is on view on
  user's screen.

Users can change between on-demand/continuous mode by clicking on the
"Rocq language status" item in the bottom right corner for VSCode. We
recommend pinning the language status item to see server status in
real-time.

### Goal display

By default, `rocq-lsp` will follow cursor and show goals at cursor
position. This can be tweaked in options.

The `rocq-lsp.sentenceNext` and `rocq-lsp.sentencePrevious` commands will
try to move the cursor one Rocq sentence forward / backwards. These
commands are bound by default to `Alt + N` / `Alt + P` (`Cmd` on
MacOS).

### Incremental proof edition

Once you have setup your basic proof style, you may want to work with
`rocq-lsp` in a way that is friendly to incremental checking.

For example, `rocq-lsp` will recognize blocks of the form:
```rocq
Lemma foo : T.
Proof.
 ...
Qed.
```

and will allow you to edit inside the `Proof.` `Qed.` block without
re-checking what is outside.

### Error recovery

`rocq-lsp` can recover many errors automatically and allow you to
continue document edition later on.

For example, it is not necessary to put `Admitted` in proofs that are
not fully completed. Also, you can work with bullets and `rocq-lsp`
will automatically admit unfinished ones, so you can follow the
natural proof structure.

### Server Status



### Embedded Markdown and LaTeX documents

`rocq-lsp` supports checking of TeX and Markdown document with embedded
Rocq inside. As of today, to enable this feature you must:

- **markdown**: open a file with `.mv` extension, `rocq-lsp` will
  recognize code blocks starting with ````coq` and ````rocq`.
- **TeX**: open a file with `.lv` extension, `rocq-lsp` will recognize
  code blocks delimited by `\begin{rocq} ... \end{rocq}` and `\begin{coq} ... \end{coq}`.

As of today, delimiters are expected at the beginning of the line,
don't hesitate to request for further changes based on this feature.

## Rocq LSP Settings

### Goal display

Several settings for goal display exist.

### Continuous vs on-demand mode:

A setting to have `rocq-lsp` check documents continuously exists.

## Memory management

You can tell the server to free up memory with the "Coq LSP: Free
memory" command.

## Advanced: Multiple Workspaces

`rocq-lsp` does support projects that combine multiple Rocq project
roots in a single workspace. That way, one can develop on several
distinct Rocq developments seamlessly.

To enable this, use the "Add Folder" option in VSCode, where each root
must be a folder containing a `_RocqProject` or `_CoqProject` file.

Check the example at
[../../examples/multiple_workspaces/](../../examples/multiple_workspaces/)
to see it in action!

## Interrupting rocq-lsp

When a Rocq document is being checked, it is often necessary to
_interrupt_ the checking process, for example, to check a new version,
or to retrieve some user-facing information, such as goals.

`rocq-lsp` supports two different interruption methods, selectable at
start time via the `--int_backend` command-line parameter:

- Rocq-side polling (`--int_backend=Coq`, default for OCaml 5.x): in
  this mode, Rocq polls for a flag every once in a while, and will
  raise an interruption when the flag is set. This method has the
  downside that some paths in Rocq don't check the flag often enough,
  for example, `Qed.`, so users may face unresponsiveness, as our
  server can only run one thread at a time.

- `memprof-limits` token-based interruption (`--int_backend=Mp`,
  experimental, default for OCaml 4.x): in this mode, Rocq will use the
  `memprof-limits` library to interrupt Rocq.

Rocq has some bugs w.r.t. handling of asynchronous interruptions coming
from `memprof-limits`. The situation is better in Rocq 8.20, but users
on Rocq <= 8.19 do need to install a version of Rocq with the backported
fixes. See the information about Rocq upstream bugs in the README for
more information about available branches.

`rocq-lsp` will reject to enable the new interruption mode by default
on Rocq < 8.20 unless the `lsp` Rocq branch version is detected.

## Advanced incremental tricks

You can use the `Reset $id` and `Back $steps` commands to isolate
parts of the document from each other in terms of rechecking.

For example, the command `Reset $id` will make the parts of the
document after it use the state before the node `id` was found. Thus,
any change between `$id` and the `Reset $id` command will not trigger
a recheck of the rest of the document.

```rocq
(* Rocq code 1 *)

Lemma foo : T.
Proof. ... Qed.

(* Rocq code 2 *)

Reset foo.

(* Rocq code 3 *)
```

In the above code, any change in the "`Rocq code 2`" section will not
trigger a recheck of the "`Rocq code 3`" Section, by virtue of the
incremental engine.

Using `Reset Initial`, you can effectively partition the document on
`N` parts! This is pretty cool for some use cases!

## Version support

`rocq-lsp` supports Rocq 9.1, Rocq 9.0, Coq 8.20, and Rocq's `master`
branch. Code for each Rocq version can be found in the corresponding
branch. We support OCaml 4.14, 5.3, and 5.4.
