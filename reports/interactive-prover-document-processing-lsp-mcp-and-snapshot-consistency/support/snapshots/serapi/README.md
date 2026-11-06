**Note**: Coq SerAPI has now stopped development, the 0.20 release for
Coq 8.20 will be the last managed by us. Coq SerAPI has been succeeded
by [coq-lsp](https://github.com/ejgallego/coq-lsp/), which solves many
longstanding issues and feature requests.

See https://github.com/ejgallego/coq-serapi/issues/252 for more
information. The `serlib` component of this repository now lives in
the `coq-lsp` repository..

New maintainers for SerAPI are **much welcome** ! Please see
https://github.com/coq-community/manifesto/issues/160 if you would
like to help keeping SerAPI maintained.

We'd like to thanks all the people that have contributed in one way or
another to SerAPI after all these years, without you neither SerAPI or
`coq-lsp` would have been possible.

## SerAPI: Machine-Friendly, Data-Centric Serialization for Coq

[![Build Status][action-badge]][action-link]
[![Zulip][zulip-badge]][zulip-link]

[action-badge]: https://github.com/ejgallego/coq-serapi/actions/workflows/ci.yml/badge.svg?branch=v8.16
[action-link]: https://github.com/ejgallego/coq-serapi/actions/workflows/ci.yml?query=branch%3Av8.16

[zulip-badge]: https://img.shields.io/badge/Zulip-chat-informational.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/256331-SerAPI

To install with opam:
```
$ opam install coq-serapi
$ sertop --help
```

Alternatively, if you use Nix:
```
$ nix-shell -p coq_8_13 coqPackages_8_13.serapi
$ sertop --help
```

SerAPI is a library for machine-to-machine interaction with the [Coq proof assistant](https://coq.inria.fr),
with particular emphasis on applications in IDEs, code analysis tools, and machine learning.
SerAPI provides automatic serialization of Coq's internal
[OCaml](https://ocaml.org) datatypes from/to [JSON](https://www.json.org) or
[S-expressions](https://en.wikipedia.org/wiki/S-expression) (sexps).

SerAPI is a proof-of-concept and should be considered
alpha-quality. However, it is fully functional and supports, among
other things, asynchronous proof checking, full-document parsing, and
serialization of Coq's core datatypes. SerAPI can also be run as
[WebWorker](https://developer.mozilla.org/en-US/docs/Web/API/Web_Workers_API/Using_web_workers)
thread, providing a self-contained Coq system inside the
browser. Typical load times in Google Chrome are less than a second.

The main design philosophy of SerAPI is to **make clients' lives easy**,
by providing a convenient, robust interface that hides most
of the scary details involved in interacting with Coq.

Feedback from Coq users and developers is very welcome and _intrinsic_
to the project. We are open to implementing new features and exploring
new use cases.

### Documentation and Help:

- [Protocol Documentation](http://ejgallego.github.io/coq-serapi/coq-serapi/Serapi/Serapi_protocol/)
- [interface file](serapi/serapi_protocol.mli)
- [SerAPI's FAQ](notes/FAQ.md)
- [technical report](https://hal-mines-paristech.archives-ouvertes.fr/hal-01384408)
- [issue tracker](https://github.com/ejgallego/coq-serapi/issues)
- [Zulip chat](https://coq.zulipchat.com/#narrow/stream/256331-SerAPI)
- [Gitter chat](https://gitter.im/coq-serapi/Lobby) channel (legacy)
- [mailing list](https://x80.org/cgi-bin/mailman/listinfo/jscoq)

**API WARNING:** _The protocol is experimental and may change often_.

### Quick Overview and Install:

SerAPI can be installed as the [OPAM](https://opam.ocaml.org) package `coq-serapi`
or the [Nix](https://nixos.org) package `coqPackages_8_13.serapi`.
See [build instructions](notes/build.md) for manual installation. The experimental
[in-browser version](https://x80.org/rhino-hawk) is also online.

SerAPI provides an interactive "Read-Print-Eval-Loop" `sertop`, a
batch-oriented compiler `sercomp`, and a batch-oriented tokenizer `sertok`.
See the manual pages and `--help` pages of each command for more details.

To get familiar with SerAPI we recommend launching the `sertop` REPL,
as it provides a reasonably human-friendly experience:

```
$ rlwrap sertop --printer=human
```

You can then input commands. `Ctrl-C` will interrupt a busy Coq
process in the same way it interrupts `coqtop`.

The program `sercomp` provides a command-line interface to some
key functionality of SerAPI and can be used for batch processing
of Coq documents, e.g., to serialize Coq source files from/to lists of
S-expressions of Coq vernacular sentences. See `sercomp --help` for some
usage examples and an overview of the main options. The program `sertok`
provides similar functionality at the level of Coq source file tokens.

### Protocol Commands:

Interaction with `sertop` is done using _commands_, which can be optionally tagged in the form of `(tag cmd)`; otherwise, an automatic tag will be assigned.
For every command, SerAPI **will always** reply with `(Answer tag Ack)` to indicate that the command was successfully parsed and delivered to Coq, or with a `SexpError` if parsing failed.

There are three categories of [commands](serapi/serapi_protocol.mli#L147):

- **Document manipulation:** `Add`, `Cancel`, `Exec`, ...: these commands instruct Coq to perform some action on the current document.
  Every command will produce zero or more different _tagged_ [answers](serapi/serapi_protocol.mli#52), and  a final answer `(Answer tag Completed)`, indicating that there won't be more output.

  SerAPI document commands are an evolution of the OCaml STM API, [here](https://github.com/ejgallego/jscoq/blob/master/etc/notes/coq-notes.md) and [here](https://github.com/siegebell/vscoq/blob/master/CoqProtocol.md) you can find a few informal notes on how it works. We are working on a more detailed specification, for now you can get some more details in the issue tracker.

- **Queries:** `(Query ((opt value) ...) kind)`:

  Queries stream Coq objects of type `kind`. This can range from options, goals and hypotheses, tactics, etc.
  The first argument is a list of options: `preds` is a list of conjunctive filters, `limit` specifies how many values the query may return.
  `pp` controls the output format: `PpSer` for full serialization, or `PpStr` for "pretty printing". For instance:
  ```lisp
  (tag (Query ((preds (Prefix "Debug")) (limit 10) (pp PpSexp)) Option))
  ```
  will stream all Coq options that start with "Debug", limiting to the first 10 and printing the full internal Coq datatype:
  ```lisp
  (CoqOption (Default Goal Selector)
     ((opt_sync true) (opt_depr false) (opt_name "default goal selector")
     (opt_value (StringValue 1))))
  ...
  ```
  Options can be omitted, as in: `(tag (Query ((limit 10)) Option))`, and
  currently supported queries can be seen [here](serapi/serapi_protocol.mli#L118)

- **Printing:** `(Print opts obj)`: The `Print` command provides access to the Coq pretty printers.
  Its intended use is for printing (maybe IDE manipulated) objects returned by `Query`.

### Roadmap and Developer organization:

SerAPI is organized in branches corresponding to upstream Coq
versions; usually, branch v8.XX is compatible with Coq 8.XX, and
corresponds to SerAPI 0.XX. These branches are stable and can be
relied upon.

The branch `main` tracks Coq `master` branch, and it is not a stable
branch; force pushes and random rebases can happen there; handle with
care!

We are working on fixing this problematic setup, which is that way as
in the past such branch used to be "private", but now that SerAPI is
in Coq's CI the development workflow has changed, with developer
submitting PRs to it.

These days, most work related to SerAPI is directly happening over
[Coq's upstream](https://github.com/coq/coq) itself. The main
objective is to improve the proof-document model; building a rich
query language will be next. See the [roadmap issue]() in our bug
tracker for more information about roadmap and the [Developer
Information](#Developer-information) section for more details on the
development setup.

### Clients and Users:

SerAPI has been used in a few contexts already, we provide a few
pointers here, feel free to add your own!

- [jsCoq](https://github.com/ejgallego/jscoq) allows you to run Coq in
  your browser. jsCoq is the predecessor of SerAPI and will shortly be
  fully based on it.
- [mCoq](https://github.com/EngineeringSoftware/mcoq) is a tool for mutation analysis
  of Coq projects, based on serializing and deserializing Coq code via SerAPI.
  See the accompanying [tool paper](https://users.ece.utexas.edu/~gligoric/papers/JainETAL20mCoqTool.pdf),
  and the [research paper](https://users.ece.utexas.edu/~gligoric/papers/CelikETAL19mCoq.pdf)
  which describes and evaluates the technique.
- [elcoq](https://github.com/cpitclaudel/elcoq), an emacs technology
  demo based on SerAPI by [Clément Pit-Claudel](https://github.com/cpitclaudel). `elcoq` is not fully
  functional but illustrates some noteworthy features of SerAPI.
- [PeaCoq](https://github.com/Ptival/PeaCoq), a Coq IDE for the
  browser, has an experimental branch that uses SerAPI.
- [GrammaTech's Software Evolution Library (SEL)](https://grammatech.github.io/sel/)
  provides tools for programmatically modifying and evaluating software. SEL operates
  over multiple software representations including source code in
  several languages and compiled machine code. Its Coq module uses
  SerAPI to serialize Coq source code into ASTs, which are parsed into
  Common Lisp objects for further manipulation. GrammaTech uses this
  library to synthesize modifications to software so that it satisfies
  an objective function, e.g., a suite of unit tests.
  SerAPI support was added to SEL by Rebecca Swords.
- [CoqGym](https://github.com/princeton-vl/CoqGym) is a Coq-based learning environment for theorem proving.
  It uses SerAPI to interact with Coq and perform feature-extraction. Its author notes:

  > CoqGym relies heavily on SerAPI for serializing the internal structures of Coq.
  > I tried to use Coq's native printing functions when I started with this project,
  > but soon I found SerAPI could save a lot of the headaches with parsing Coq's output.
  > Thanks to SerAPI authors, this project wouldn't be possible (or at least in its current form) without SerAPI.

  See also the [paper](https://arxiv.org/abs/1905.09381) describing CoqGym.
- [Proverbot9001](https://github.com/UCSD-PL/proverbot9001) is a proof search system based on machine
  learning techniques, and uses SerAPI to interface with Coq.
  See also the [paper](https://arxiv.org/abs/1907.07794) describing the system.
- [Roosterize](https://github.com/EngineeringSoftware/roosterize) is a tool for
  suggesting lemma names in Coq projects based on machine learning.
  See the [paper](https://arxiv.org/abs/2004.07761) describing the technique and tool.
  Additional paper with demo: https://arxiv.org/abs/2103.01346 .
- The [paper](https://arxiv.org/abs/2006.16743) _Learning to Format Coq Code Using Language Models_
  implements a Coq code formatter.
- [MathComp corpus](https://github.com/EngineeringSoftware/math-comp-corpus) is a machine learning
  dataset based on the [Mathematical Components](https://math-comp.github.io/) family of Coq projects,
  and includes several machine-readable representations of Coq code generated via SerAPI.
  The dataset was used to train and evaluate the Roosterize tool.
- A Python interface for SerAPI can be found at [PyCoq](https://github.com/IBM/pycoq)
- A direct Python interface to Coq, using `serlib` can be found at https://github.com/ejgallego/pyCoq
- SerAPI is being used to improve the Coq regression proof
  selection tool [iCoq](https://cozy.ece.utexas.edu/icoq/),
  see the [paper](https://users.ece.utexas.edu/~gligoric/papers/CelikETAL17iCoq.pdf).
- SerAPI is being used in additional software testing and machine learning projects; we will
  update this list as papers get out of embargo.

### Quick Demo (not always up to date):

```lisp
$ rlwrap sertop --printer=human
(Add () "Lemma addn0 n : n + 0 = n. Proof. now induction n. Qed.")
  > (Answer 0 Ack)
  > (Answer 0 (Added 2 ((fname "") (line_nb 1) (bol_pos 0) (line_nb_last 1) (bol_pos_last 0) (bp 0) (ep 26))
  >            NewTip))
  > ...
  > (Answer 0 (Added 5 ... NewTip))
  > (Answer 0 Completed)

(Exec 5)
  > (Answer 1 Ack)
  > (Feedback ((id 5) (route 0) (contents (ProcessingIn master))))
  > ...
  > (Feedback ((id 5) (route 0) (contents Processed)))
  > (Answer 1 Completed)

(Query ((sid 3)) Goals)
  > (Answer 2 Ack)
  > (Answer 2
  >  (ObjList ((CoqGoal ((fg_goals (((name 5) (ty (App (Ind ...))))
                         (bg_goals ()) (shelved_goals ()) (given_up_goals ()))))))
  > (Answer 2 Completed)

(Query ((sid 3) (pp ((pp_format PpStr)))) Goals)
  > (Answer 3 Ack)
  > (Answer 3 (ObjList ((CoqString
  >   "\
  >    \n  n : nat\
  >    \n============================\
  >    \nn + 0 = n"))))
  > (Answer 3 Completed)

(Query ((sid 4)) Ast)
  > (Answer 4 Ack)
  > (Answer 4 (ObjList ((CoqAst ((((fname "") (line_nb 1) (bol_pos 0) (line_nb_last 1)
  >                                (bol_pos_last 0) (bp 34) (ep 50)))
  > ...
  >            ((Tacexp
  >              (TacAtom
  >                (TacInductionDestruct true false
  > ...
  > (Answer 4 Completed)

(pp_ex (Print ((sid 4) (pp ((pp_format PpStr)))) (CoqConstr (App (Rel 0) ((Rel 0))))))
  > (Answer pp_ex Ack)
  > (Answer pp_ex(ObjList((CoqString"(_UNBOUND_REL_0 _UNBOUND_REL_0)"))))

(Query () (Vernac "Print nat. "))
  > (Answer 6 Ack)
  > (Feedback ((id 5) (route 0) (contents
  >    (Message Notice ()
  >    ((Pp_box (Pp_hovbox 0) ...)
  > (Answer 6 (ObjList ()))
  > (Answer 6 Completed)

(Query () (Definition nat))
  > (Answer 7 Ack)
  > (Answer 7 (ObjList ((CoqMInd (Mutind ....)))))
  > (Answer 7 Completed)
```

### Technical Report:

There is a brief [technical report](https://hal-mines-paristech.archives-ouvertes.fr/hal-01384408)
describing the motivation, design, and implementation of SerAPI. If you are using
SerAPI in a project, please cite the technical report in any related publications:

```bibtex
@techreport{GallegoArias2016SerAPI,
  title = {{SerAPI: Machine-Friendly, Data-Centric Serialization for Coq}},
  author = {Gallego Arias, Emilio Jes{\'u}s},
  url = {https://hal-mines-paristech.archives-ouvertes.fr/hal-01384408},
  institution = {MINES ParisTech},
  year = {2016},
  month = Oct,
}
```

## Developer Information

### Technical Details

SerAPI has four main components:

- `serapi`, an extended version of the current IDE protocol;
- `serlib`, a library providing automatic de/serialization of most Coq data structures using `ppx_conv_sexp`. This should be eventually incorporated into Coq itself. Support for `ppx_deriving_yojson` is work in progress;
- `sertop`, `sertop_js`, toplevels offering implementations of the protocol;
- `sercomp`, `sertok`, command-line tools providing access to key features of `serlib`.

Building your own toplevels using `serlib` and `serapi` is encouraged.

### Advanced Use Cases

With a bit more development effort, you can also:

- Use SerAPI as an OCaml library. The low-level serialization library
  [`serlib/`](/serlib) and the higher-level SerAPI protocol in
  [`serapi/serapi_protocol.mli`](/serapi/serapi_protocol.mli) can be
  linked standalone.

- Use SerAPI's web worker [JavaScript Worker](https://developer.mozilla.org/en-US/docs/Web/API/Web_Workers_API/Using_web_workers)
  from your web/node application. In this model, you communicate with SerAPI using
  the typical `onmessage/postMessage` worker API. Ready-to-use builds
  may be found at
  [here](https://github.com/ejgallego/jscoq-builds/tree/serapi), we
  provide an example REPL at: https://x80.org/rhino-hawk

We would also like to provide a [Jupyter/IPython kernel](https://github.com/ejgallego/coq-serapi/issues/17).

### Developer/Users Mailing List

SerAPI development is mainly discussed [on GitHub](https://github.com/ejgallego/coq-serapi)
and in the [Gitter channel](https://gitter.im/coq-serapi/Lobby).
You can also use the jsCoq mailing list by subscribing at:
https://x80.org/cgi-bin/mailman/listinfo/jscoq

The mailing list archives should also be available at the Gmane group:
`gmane.science.mathematics.logic.coq.jscoq`. You can post to the list
using nntp.

## Acknowledgments

SerAPI has been developed at the
[Centre de Recherche en Informatique](https://www.cri.ensmp.fr) of
[MINES ParisTech](http://www.mines-paristech.fr/) (former École de
Mines de Paris) and was partially supported by the
[FEEVER](http://www.feever.fr) project.
