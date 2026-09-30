# Rocq LSP <img align="right" height="42" src="./etc/img/inria-logo.png"/>  <!-- omit in toc -->

[![Github CI][ci-badge]][ci-link]

`rocq-lsp` is a [Language Server](https://microsoft.github.io/language-server-protocol/) for the [Rocq Prover](https://rocq-prover.org/). It provides a single server that implements:

- the [LSP](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/)
  protocol, with custom [extensions](./etc/doc/PROTOCOL.md)
- the [petanque](./petanque) protocol, designed for low-latency interaction with
  Rocq, idel for AI and software engineering applications
- the [MCP](https://modelcontextprotocol.io/) protocol (upcoming), an open
  protocol that standardizes how applications provide context to LLMs

**☕ Try it online ☕**:  https://github.dev/ejgallego/hello-rocq

**Key [features](#Features)** of `rocq-lsp` are: continuous, incremental document
checking, real-time interruptions and limits, programmable error recovery,
literate Markdown and LaTeX document support, multiple workspaces, positional
goals, information panel, performance data, completion, jump to definition,
extensible command-line compiler, a plugin system, and more.

`rocq-lsp` is built on **Flèche**, a new document checking engine for formal
documents based on our previous work on
[SerAPI](https://github.com/ejgallego/coq-serapi/) and
[jsCoq](https://github.com/jscoq/jscoq).

Designed for interactive use and web-native environments, Flèche is extensible
and supports [advanced tooling integration](#-a-platform-for-research) and
capabilities beyond standard Rocq.

See the [User Manual](./etc/doc/USER_MANUAL.md) and the [General Documentation Index](./etc/doc/) for more details.

This repository also includes the `rocq-lsp` [Visual Studio
Code](https://code.visualstudio.com/) editor extension for the [Rocq Proof
Assistant](https://rocq-prover.org/), and a few other components. See our
[contributing guide](#contributing) for more information. Support
for [Emacs](#emacs), [Vim](#vim) and [Neovim](#neovim) is also available in
their own projects.

**Citation**

You can cite Rocq-lsp technical report and code repository as follows:

```bibtex
@software{rocq-lsp,
  author       = {Gallego Arias, Emilio Jesús and rocq-lsp contributors},
  title        = {Rocq-lsp: Visual Studio Code Extension and Language Server Protocol for Rocq}
  year         = {2025},
  version      = {v0.2.5},
  url          = {https://github.com/ejgallego/rocq-lsp},
  urldate      = {2025-11-30},
  note         = {GitHub repository}
}

@techreport{2025:fleche,
  author       = {Gallego Arias, Emilio Jesús},
  title        = {Flèche: Incremental Validation for Hybrid Formal Documents},
  institution  = {IRIF, CNRS, Univ. Paris Cité, INRIA},
  year         = {2025},
  date         = {2025-11-30}
}
```

**Quick Install**:

  - **🐧 Linux / 🍎 macOs / 🪟 Windows:**
```
$ opam install coq-lsp && code --install-extension ejgallego.coq-lsp
```

  - **🦄 Emacs**:

```elisp
 (use-package rocq-mode
    :vc (:url "https://codeberg.org/jpoiret/rocq-mode.el.git"
         :rev :newest)
    :mode "\\.v\\'"
    :hook
    (rocq-mode . rocq-follow-viewport-mode)
    (rocq-mode . rocq-auto-goals-at-point-mode))
```

  - **🪟 Windows:** (alternative method)

    Download the [Rocq Platform installer](#-server)

## Table of Contents <!-- omit in toc -->

- [🎁 Features](#-features)
  - [⏩ Incremental Compilation and Continuous Document Checking](#-incremental-compilation-and-continuous-document-checking)
  - [👁 On-demand, Follow The Viewport Document Checking](#-on-demand-follow-the-viewport-document-checking)
  - [🧠 Smart, Cache-Aware Error Recovery](#-smart-cache-aware-error-recovery)
  - [🥅 Whole-Document Goal Display](#-whole-document-goal-display)
  - [🗒️ Markdown Support](#️-markdown-and-latex-support)
  - [👥 Document Outline](#-document-outline)
  - [🐝 Document Hover](#-document-hover)
  - [📁 Multiple Workspaces](#-multiple-workspaces)
  - [💾 `.vo` file saving](#-vo-file-saving)
  - [⏱️ Detailed Timing and Memory Statistics](#️-detailed-timing-and-memory-statistics)
  - [🔧 Client-Side Configuration Options](#-client-side-configuration-options)
  - [🖵 Extensible, Machine-friendly Command Line Compiler](#️-extensive-machine-friendly-command-line-compiler)
  - [♻️ Reusability, Standards, Modularity](#️-reusability-standards-modularity)
  - [🌐 Web Native!](#-web-native)
  - [🔎 A Platform for Research!](#-a-platform-for-research)
- [🛠️ Installation](#️-installation)
  - [🏘️ Supported Rocq (and Coq) Versions](#️-supported-rocq-versions)
  - [🏓 Server](#-server)
  - [🫐 Visual Studio Code](#-visual-studio-code)
  - [🦄 Emacs](#-emacs)
  - [✅ Vim](#-vim)
  - [🩱 Neovim](#-neovim)
  - [🐍 Python](#-python)
- [⇨ `rocq-lsp` users and extensions](#-rocq-lsp-users-and-extensions)
- [🗣️ Discussion Channel](#️-discussion-channel)
- [☎ Weekly Calls](#-weekly-calls)
- [❓FAQ](#faq)
- [⁉️ Troubleshooting and Known Problems](#️-troubleshooting-and-known-problems)
  - [📂 Working With Multiple Files](#-working-with-multiple-files)
- [📔 Planned Features](#-planned-features)
- [📕 Protocol Documentation](#-protocol-documentation)
- [🤸 Contributing and Extending the System](#-contributing-and-extending-the-system)
- [🥷 Team](#-team)
  - [🕰️ Past Contributors](#️-past-contributors)
- [©️ Licensing Information](#️-licensing-information)
- [👏 Acknowledgments](#-acknowledgments)

## 🎁 Features

### ⏩ Incremental Compilation and Continuous Document Checking

Edit your file, and `rocq-lsp` will try to re-check only what is necessary,
continuously. No more dreaded `Ctrl-C Ctrl-N`! Rechecking tries to be smart,
and will ignore whitespace changes.

<img alt="Incremental checking" height="286px" src="etc/img/lsp-incr.gif"/>

In a future release, `rocq-lsp` will save its document cache to disk, so you can
restart your proof session where you left it at the last time.

Incremental support is undergoing refinement, if `rocq-lsp` rechecks when it
should not, please file a bug!

### 👁 On-demand, Follow The Viewport Document Checking

`rocq-lsp` does also support on-demand checking. Two modes are available: follow
the cursor, or follow the viewport; the modes can be toggled using the Language
Status Item in Code's bottom right corner:

<img alt="On-demand checking" height="572px" src="etc/img/on_demand.gif"/>

### 🧠 Smart, Cache-Aware Error Recovery

`rocq-lsp` won't stop checking on errors, but supports (and encourages) working
with proof documents that are only partially working. Error recovery integrates
with the incremental cache, and does recognize proof structure.

You can edit without fear inside a `Proof. ... Qed.`, the rest of the document
won't be rechecked; you can leave bullets and focused goals unfinished, and
`rocq-lsp` will automatically admit them for you.

If a lemma is not completed, `rocq-lsp` will admit it automatically. No more
`Admitted` / `Qed` churn!

<img alt="Smart error recovery" height="286px" src="etc/img/lsp-errors.gif"/>

### 🥅 Whole-Document Goal Display

`rocq-lsp` will follow the cursor movement and show underlying goals and
messages; as well as information about what goals you have given up, shelves,
pending obligations, open bullets and their goals.

<img alt="Whole-Document Goal Display" height="286px" src="etc/img/lsp-goals.gif"/>

Goal display behavior is configurable in case you'd like to trigger goal display
more conservatively.

### 🗒️ Markdown and LaTeX Support

Open a markdown file with a `.mv` extension, or a `TeX` file ending in `.lv` or
`.v.tex`, then `rocq-lsp` will check the code parts that are enclosed into `rocq`
language blocks! `rocq-lsp` places human-friendly documents at the core of its
design ideas.

<img alt="Rocq + Markdown Editing" height="286px" src="etc/img/lsp-markdown.gif"/>

Moreover, you can use the usual Visual Studio Code Markdown or LaTeX preview
facilities to render your markdown documents nicely!

### 👥 Document Outline

`rocq-lsp` supports document outline and code folding, allowing you to jump
directly to definitions in the document. Many of the Rocq vernacular commands
like `Definition`, `Theorem`, `Lemma`, etc. will be recognized as document
symbols which you can navigate to or see the outline of.

<img alt="Document Outline Demo" height="286px" src="etc/img/lsp-outline.gif"/> <img alt="Document Symbols" height="286px" src="etc/img/lsp-doc-symbols.png"/>

### 🐝 Document Hover

Hovering over a Rocq identifier will show its type.

<img alt="Types on Hover" height="286px" src="etc/img/lsp-hover-2.gif"/>

Hover is also used to get debug information, which can be enabled in the
preferences panel.

### 📁 Multiple Workspaces

`rocq-lsp` supports projects with multiple `_RocqProject` (or `_CoqProject`) files, use the "Add
folder to Workspace" feature of Visual Studio code or the LSP Workspace Folders
extension to use this in your project.

### 💾 `.vo` file saving

`rocq-lsp` can save a `.vo` file of the current document as soon as it the
checking has been completed, using the command `Coq LSP: Save file to .vo`.

You can configure `rocq-lsp` in settings to do this every time you save your
`.vo` file, but this can be costly so we ship it disabled by default.

### ⏱️ Detailed Timing and Memory Statistics

Hover over any Rocq sentence, `rocq-lsp` will display detailed memory and timing
statistics.

<img alt="Stats on Hover" height="286px" src="etc/img/lsp-hover.gif"/>

### 🔧 Client-Side Configuration Options

`rocq-lsp` is configurable, and tries to adapt to your own workflow. What to do
when a proof doesn't check, admit or ignore? You decide!

See the `rocq-lsp` extension configuration in VSCode for options available.

<img alt="Configuration screen" height="286px" src="etc/img/lsp-config.png"/>

### 🖵 Extensible, Machine-friendly Command Line Compiler

`rocq-lsp` includes the `fcc` "Flèche Coq Compiler" which allows the access to
almost all the features of Flèche / `rocq-lsp` without the need to spawn a
fully-fledged LSP client.

`fcc` has been designed to be machine-friendly and extensible, so you can easily
add your pre/post processing passes, for example to analyze or serialize parts
of Rocq files.

### 🪄 Advanced APIs for Rocq Interaction

Thanks to Flèche, we provide some APIs on top of it that allow advanced use
cases with Rocq. In particular, we provide direct, low-overhead access to Rocq's
proof engine using [petanque](./petanque).

### ♻️ Reusability, Standards, Modularity

The incremental document checking library of `rocq-lsp` has been designed to be
reusable by other projects written in OCaml and with needs for document
validation UI, as well as by other Rocq projects such as jsCoq.

Moreover, we are strongly based on standards, aiming for the least possible
extensions.

### 🌐 Web Native!

`rocq-lsp` has been designed from the ground up to fully run inside your web
browser seamlessly; our sister project, [jsCoq](https://github.com/jscoq/jscoq)
has been already been ported to `rocq-lsp`, and future releases
will use it by default.

`rocq-lsp` provides an exciting new array of opportunities for jsCoq, lifting
some limitations we inherited from Rocq's lack of web native support.

### 🔎 A Platform for Research!

A key `rocq-lsp` goal is to serve as central platform for researchers in
Human-Computer-Interaction, Machine Learning, and Software Engineering willing
to interact with Rocq.

Towards this goal, `rocq-lsp` extends and is in the process of replacing [Coq
SerAPI](https://github.com/ejgalleg/coq-serapi), which has been used by many to
that purpose.

If you are a SerAPI user, please see our preliminary [migrating from
SerAPI](etc/SerAPI.md) document.

## 🛠️ Installation

In order to use `rocq-lsp` you'll need to install [**both**](etc/FAQ.md)
`rocq-lsp` and a suitable LSP client that understands `rocq-lsp` extensions. The
recommended client is the Visual Studio Code Extension, but we aim to fully
support other clients officially and will do so once their authors consider them
ready.

### 🏘️ Supported Rocq and OCaml Versions

`rocq-lsp` supports Rocq 9.2, Rocq 9.1, Rocq 9.0, Coq 8.20, and Rocq's `master`
branch. Code for each Rocq version can be found in the corresponding branch. We
support OCaml 4.14, 5.3, and 5.4.

We recommended using Rocq 9.2 or `master` version. For other Rocq versions, we
recommend users to install the custom Rocq tree as detailed in [Rocq Upstream
Bugs](#rocq-upstream-bugs).

Note that this section covers user installs, if you would like to contribute to
`rocq-lsp` and build a development version, please check our [contributing
guide](./CONTRIBUTING.md)

### 🏓 Server

- **opam** (OSX/Linux):
  ```
  opam install coq-lsp
  ```
- **Nix**:
  - In nixpkgs: [coqPackages.coq-lsp](https://github.com/NixOS/nixpkgs/tree/master/pkgs/development/coq-modules/coq-lsp)
  - The `rocq-lsp` server is automatically put in scope when running `nix-shell` in a
    project using the [Rocq Nix Toolbox](https://github.com/rocq-community/coq-nix-toolbox)
    (added to the toolbox Oct 10th 2023).
  - An example of a `flake` that uses `rocq-lsp` in a development environment is here
     https://github.com/HoTT/Coq-HoTT/blob/master/flake.nix .
- **Windows**:
  Experimental Windows installers based on the [Rocq
  Platform](https://github.com/rocq-prover/platform) are available at https://www.irif.fr/~gallego/coq-lsp/

  This provides a Windows native binary that can be executed from VSCode
  normally. As of today a bit of configuration is still needed:
  - In VSCode, set the `Coq-lsp: Path` to:
    + `C:\Coq-Platform~8.20-lsp\bin\coq-lsp.exe`
  - In VSCode, set the `Coq-lsp: Args` to:
    + `--coqlib=C:\Coq-Platform~8.20-lsp\lib\coq\`
    + `--coqcorelib=C:\Coq-Platform~8.20-lsp\lib\coq-core\`
    + `--ocamlpath=C:\Coq-Platform~8.20-lsp\lib\`
  - Replace `C:\Coq-Platform~8.20-lsp\` by the path you have installed Rocq above as needed
  - Note that the installers are unsigned (for now), so you'll have to click on
    "More info" then "Run anyway" inside the "Windows Protected your PC" dialog
  - Also note that the installers are work in progress, and may change often.
- **Do it yourself!** [Compilation from sources](./CONTRIBUTING.md#compilation)

<!-- TODO 🟣 Emacs, 🪖 Proof general, 🐔 RocqIDE -->

### 🫐 Visual Studio Code

- Official Marketplace: https://marketplace.visualstudio.com/items?itemName=ejgallego.coq-lsp
- Open VSX: https://open-vsx.org/extension/ejgallego/coq-lsp

### 🦄 Emacs

The official Rocq Emacs mode is https://codeberg.org/jpoiret/rocq-mode.el ,
maintained by Josselin Poiret with contributions by Arthur Azevedo de Amorim.

### ✅ Vim

- Experimental [CoqTail](https://github.com/whonore/Coqtail) support by Wolf Honore:
  https://github.com/whonore/Coqtail/pull/323

  See it in action https://asciinema.org/a/mvzqHOHfmWB2rvwEIKFjuaRIu

### 🩱 Neovim

- Experimental client by Jaehwang Jung: https://github.com/tomtomjhj/coq-lsp.nvim

### 🐍 Python

- Interact programmatically with Rocq files by using the [Coqpyt](https://github.com/sr-lab/coqpyt)
  by Pedro Carrott and Nuno Saavedra.

### OCaml

- [`rocq-lsp-client`](https://github.com/proof-ninja/rocq-lsp-client) by [Yoshihiro Imai](https://yoshihiro503.github.io/home_en.html)/[Proof Ninja](https://proof-ninja.co.jp/).

## ⇨ `rocq-lsp` users and extensions

The below projects are using `rocq-lsp`, we recommend you try them!

- [Coqpyt, a Python client for rocq-lsp](https://github.com/sr-lab/coqpyt)
- [CoqPilot uses Large Language Models to generate multiple potential proofs and then uses rocq-lsp to typecheck them](https://github.com/JetBrains-Research/coqpilot).
- [jsCoq: use Coq from your browser](https://github.com/jscoq/jscoq)
- [Pytanque: a Python library implementing RL Environments](https://github.com/LLM4Coq/pytanque)
- [ViZX: A Visualizer for the ZX Calculus](https://github.com/inQWIRE/ViZX).
- [The Waterproof vscode extension helps students learn how to write mathematical proofs](https://github.com/impermeable/waterproof-vscode).
- [Yade: Support for the YADE diagram editor in VSCode](https://github.com/amblafont/vscode-yade-example).

## 🗣️ Discussion Channel

`rocq-lsp` discussion channel it at [Rocq's
Zulip](https://rocq-prover.zulipchat.com/#narrow/channel/329642-coq-lsp), don't hesitate
to stop by; both users and developers are welcome.

## ☎ Weekly Calls

We hold (almost) weekly video conference calls, see the [Call Schedule
Page](https://github.com/ejgallego/rocq-lsp/wiki/Rocq-Lsp-Calls) for more
information. Everyone is most welcome!

## ❓FAQ

See our [list of frequently-asked questions](./etc/FAQ.md).

## ⁉️ Troubleshooting and Known Problems

### Rocq upstream bugs

Unfortunately Rocq releases contain bugs that affect `rocq-lsp`. We strongly
recommend that if you are installing via opam, you use the following branches
that have some fixes backported:

- For 9.1: No known critical problems
- For 9.0: No known critical problems
- For 8.20: No known critical problems
- For 8.19: `opam pin add coq-core https://github.com/ejgallego/coq.git#v8.19+lsp`
- For 8.18: `opam pin add coq-core https://github.com/ejgallego/coq.git#v8.18+lsp`
- For 8.17: `opam pin add coq-core https://github.com/ejgallego/coq.git#v8.17+lsp`

### Known problems

- Current rendering code can be slow with complex goals and messages, if that's
  the case, please open an issue and set the option `Coq LSP > Method to Print
  Coq Terms` to 0 as a workaround.
- `rocq-lsp` can fail to interrupt Coq in some cases, such as `Qed` or type class
  search. If that's the case, please open an issue, we have a experimental
  branch that solves this problem that you can try.
- If you install `coq-lsp/VSCode` simultaneously with the `VSRocq` Visual Studio
  Code extension, Visual Studio Code gets confused and neither of them may
  work. `rocq-lsp` will warn about that. You can disable the `VSRocq` extension as
  a workaround.
- `_RocqProject` file parsing library will often `exit 1` on bad `_RocqProject`
  files! There is little `rocq-lsp` can do here, until upstream fixes this.

### Troubleshooting

- Some problems can be resolved by restarting `coq-lsp`, in Visual Studio Code,
  `Ctrl+Shift+P` will give you access to the `coq-lsp.restart` command.
  You can also start / stop the server from the status bar.
- In VSCode, the "Output" window will have a "Coq LSP Server Events" channel
  which should contain some important information; the content of this channel
  is controlled by the `Coq LSP > Trace: Server` option.

## 📔 Planned Features

See [planned features and contribution ideas](etc/ContributionIdeas.md) for a
list of things we'd like to happen.

## 📕 Protocol Documentation

`rocq-lsp` mostly implements the [LSP
Standard](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/),
plus some extensions specific to Rocq.

Check [the `rocq-lsp` protocol documentation](etc/doc/PROTOCOL.md) for more details.

## 🤸 Contributing and Extending the System

Contributions are very welcome! Feel free to chat with the dev team in
[Zulip](https://rocq-prover.zulipchat.com/#narrow/channel/329642-rocq-lsp) for any
question, or just go ahead and hack.

We have a [contributing guide](CONTRIBUTING.md), which includes a description of
the organization of the codebase, developer workflow, and more.

Here is a [list of project ideas](etc/ContributionIdeas.md) that could be of
help in case you are looking for contribution ideas, tho we are convinced that
the best ideas will arise from using `rocq-lsp` in your own Rocq projects.

Both Flèche and `rocq-lsp` have a preliminary _plugin system_. The VSCode
extension also exports and API so other extensions use its functionality
to query and interact with Rocq documents.

## 🥷 Team

- Rocq-community

### 🕰️ Past Contributors

- Emilio J. Gallego Arias (Inria Paris, co-coordinator)
- Ali Caglayan (co-coordinator)
- Shachar Itzhaky (Technion)
- Vincent Laporte (Inria)
- Ramkumar Ramachandra (Inria Paris)

## ©️ Licensing Information

The license for this project is LGPL 2.1 (or GPL 3+ as stated in the LGPL 2.1).

- This server forked from our previous LSP implementation for the
  [Lambdapi](https://github.com/Deducteam/lambdapi) proof assistant, written by
  Emilio J. Gallego Arias, Frédéric Blanqui, Rodolphe Lepigre, and others; the
  initial port to Rocq was done by Emilio J. Gallego Arias and Vicent Laporte.

- `serlib`, `tests`, and goal processing components (among others) come from
  [SerAPI](https://github.com/rocq-archive/coq-serapi), and are under the same
  license. SerAPI was developed by Emilio J. Gallego Arias, Karl Palmskog, and
  Clément Pit-Claudel.

- Javascript support, and server-side package management were developed in the
  [jsCoq](https://github.com/jscoq/jscoq) project, by Shachar Itzhaky and Emilio
  J. Gallego Arias.

- Syntax files in editor/code are partially derived from
  [VSCoq](https://github.com/siegebell/vscoq) by Christian J. Bell, distributed
  under the terms of the MIT license (see ./editor/code/License-vscoq.text).

## 👏 Acknowledgments

Work on this server has been made possible thanks to many discussions,
inspirations, and sharing of ideas from colleagues. In particular, we'd like to
thank Rudi Grinberg, Andrey Mokhov, Clément Pit-Claudel, and Makarius Wenzel for
their help and advice. Gaëtan Gilbert contributed many key and challenging Rocq
patches essential to `rocq-lsp`; we also thank Guillaume Munch-Maccagnoni for his
[memprof-limits](https://guillaume.munch.name/software/ocaml/memprof-limits/index.html)
library, which is essential to make `rocq-lsp` on the real world, as well for
many advice w.r.t. OCaml.

`rocq-lsp` includes several components and tests from
[SerAPI](https://github.com/rocq-archive/coq-serapi), including
[serlib](./serlib), goal display code, etc... Thanks to Karl Palmskog and all
the SerAPI contributors.

As noted above, the original implementation was based on the Lambdapi LSP
server, thanks Frédéric Blanqui, Rodolphe Lepigre and all Lambdapi contributors.

[ci-badge]: https://github.com/ejgallego/rocq-lsp/actions/workflows/build.yml/badge.svg
[ci-link]: https://github.com/ejgallego/rocq-lsp/actions/workflows/build.yml

<!-- Local Variables: -->
<!-- mode: Markdown -->
<!-- fill-column: 80 -->
<!-- End: -->
