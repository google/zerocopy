(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* SerAPI: Coq interaction protocol with bidirectional serialization    *)
(************************************************************************)
(* Copyright 2016-2019 MINES ParisTech -- License LGPL 2.1+             *)
(* Copyright 2019-2023 Inria           -- License LGPL 2.1+             *)
(* Written by: Emilio J. Gallego Arias and others                       *)
(************************************************************************)

open Ltac_plugin

(** The SerAPI Protocol *)

(** SerAPI is a set of utilities designed to help users and tool
    creators to interact with {{:https://coq.inria.fr}Coq} in a
    systematic way; in particular, SerAPI was designed to provide full
    serialization and de-serialization of key Coq structures, including
    user-level AST and kernel terms.

    SerAPI also provides a reification of Coq's document building API,
    making it pretty easy to build and check systematically Coq
    documents.

    As of today SerAPI does provide the following components:

    - [serlib]: A library providing serializers for core Coq structures;
      the main serialization formats are S-expressions and JSON. [serlib] is
    based on {{:https://github.com/janestreet/ppx_sexp_conv}ppx_sexp_conv}
    from Jane Street and `ppx_deriving_yojson`. [serlib] also provides for
    custom hash and equality functions for many Coq types.
    - [sertop]: A toplevel executable exposing a simple document building
    and querying protocol. This is the main component, we document it properly below.
    - [sercomp]: A simple compiler utility for .v files that can input and output
    Coq files in a variety of formats. See its manual for more help.
    - [serload]: TODO

{2 History:}

SerAPI was a {{:https://github.com/ejgallego/jscoq}JsCoq} offspring
project; JsCoq added experimental serialization of Coq terms, however we quickly
realized that this facility would be helpful in the general setting; we also took
advantage of the serialization facilities to specify the Coq building API as a DSL;
the client for the tool was an {{:https://github.com/cpitclaudel/elcoq}experimental Emacs mode}
by Clément Pit-Claudel.

The next step was to provide reliable "round-trip" (de)serialization of full Coq documents;
Karl Palmskog contributed the round trip testing infrastructure to make this happen.

{2 Users:}

SerAPI is a bit of a swiss army knife, in the sense that it is a general "talk to Coq" tool and can do
many things; a good way to understand the tool is look at some of its users, see the list of them in the
{{:https://github.com/ejgallego/coq-serapi/}Project's README}

*)

(** {2 Basic Overview of the Protocol: }

SerAPI protocol can be divided in two main sets of operations:
document creation and checking, and document querying.

Note that the protocol is fully specified as a DSL written in OCaml; thus, its
canonical specification can be found below as documents to the OCaml code.
In this section, we attempt a brief introduction, but the advanced user will
without doubt want to look at the details just below.

{3 Document creation and checking: }

Before you can use SerAPI to extract any information about a Coq document,
you must indeed have Coq parse and process the document. Coq's parsing process
is quite complicated due to user-extensibility, but SerAPI tries to smooth the
experience as much as possible.

A Coq document is basically a list of sentences which are uniquely identified
by a [Stateid.t] object; for our purposes this identifier is an integer.

{b Note:} {e In future versions, sentence id will be deprecated, and instead we will use
Language Server Protocol-style locations inside the document to identify sentences.}

Each sentence has a "parent", that is to say, a previous sentence; the initial sentence has as a parent [sid = 1] ([sid] = sentence id).

Note that the parent is important for parsing as it may modify the parsing itself,
for example it may be a [Notation] command.

Thus, to build or append to a Coq document, you should select a parent sentence and
ask SerAPI to add some new ones. This is achieved with the [(Add (opts) "text")] command.

See below for a detailed overview of [Add], but the basic idea is that Coq will
parse and add to the current document as many sentences as you have sent to it.
Unfortunately, sentence number for the newly added ones is not always predictable but
there are workarounds for that.

If succesfull, [Add] will send back an [Added] message with the location and
new sentence identifier. This is useful to let SerAPI do the splitting of sentences
for you. A typical use thus is:

[(Add () "Lemma addnC n : n + 0 = n. Proof. now induction n. Qed.")]

This will return 4 answers.

{4 Sentence Checking}

Adding a set of sentences basically amounts to parsing, however in most cases Coq
won't try to typecheck or run the tactics at hand. For that purpose you can use the
[(Exec sid)] command. Taking a sentence id, [Check] will actually check [sid] and
all the sentences [sid] depends upon.

Note that in some modes Coq can skip proofs here, so in order to get a fully-checked
document you may have to issue [Check] for every sentence on it. Checking a
sentence twice is usually a noop.

{4 Modification of the Document}

In order to modify a "live" document, SerAPI does provide a [(Cancel sid)] command.
[Cancel] will take a sentence id and return the list of sentences that are
not valid anymore.

Thus, you can edit a document by cancelling and re-adding sentences.

{5 Caveats}

Cancelling a non-executed part is poorly supported by the underlying Coq checking algorithm.
In particular, [Cancel] will force execution up to the previous sentence; thus it is not possible
to parse a list of sentences and then replace them without incurring in the cost of executing them.
In particular, it could be even the case that after issuing [Cancel sid], there is an error in the
execution of an unrelated sentence. It should be possible to identify this sentence using the
exception attributes. As of today, this remains a hard-limitation of the STM.

{3 Querying documents: }

For a particular point on the document, you can query Coq for information about
it. Common query use cases are for example lists of tactics, AST, completion, etc...
Querying is done using the [(Query (opts) query)] command. The full specification
can be found below.

A particulary of [Query] is that the caller must set all the pertinent output options.
For example, if the query should return for-humans data or machine-readable one.

{2 Non-interactive use }

In many cases, non-interactive use is very convenient; for that, we
recommend you read the help of the `sercomp` compiler.

*)

(** {2 Protocol Specification } *)

(******************************************************************************)
(* Basic Protocol Objects                                                     *)
(******************************************************************************)

(** {3 Basic Protocol Objects}

SerAPI can return different kinds of objects as an answer to queries; object type is
usually distinguished by a tag, for example [(CoqString "foo")] or [(CoqConstr (App ...)]

Serialization representation is derived from the OCaml representation automatically, except for a few
custom datatypes (see below). Thus, the best is to use Merlin or some OCaml-browsing tool as to know the internal of each type;
we provide a brief description of each object:
*)

type coq_object =
  | CoqString    of string
  (** A string  *)
  | CoqSList     of string list
  (** A list of strings *)
  | CoqPp        of Pp.t
  (** A Coq "Pretty Printing" Document type, main type used by Coq to submit formatted output *)
  (* | CoqRichpp    of Richpp.richpp *)
  | CoqLoc       of Loc.t
  (** A Coq Location object, used for positions inside the document. *)
  | CoqTok       of Tok.t CAst.t list
  (** Coq Tokens, as produced by the lexer  *)
  | CoqDP        of Names.DirPath.t
  (** Coq "Logical" Paths, used for module and section names *)
  | CoqAst       of Vernacexpr.vernac_control
  (** Coq Abstract Syntax trees for statements, as produced by the parser *)
  | CoqOption    of Goptions.option_name * Goptions.option_state
  (** Coq Options, as in [Set Resolution Depth] *)
  | CoqConstr    of Constr.constr
  (** Coq Kernel terms, this is the fundamental representation for terms of the Calculus of Inductive constructions *)
  | CoqEConstr   of EConstr.t
  (** Coq Kernel terms, but maybe open *)
  | CoqExpr      of Constrexpr.constr_expr
  (** Coq term ASTs, this is the user-level parsing tree of terms *)
  | CoqMInd      of Names.MutInd.t * Declarations.mutual_inductive_body
  (** Coq kernel-level inductive; this is a low-level object that contains all the details of an inductive. *)
  | CoqEnv       of Environ.env
  (** Coq kernel-level enviroments: they do provide the full information about what the kernel know, heavy. *)
  | CoqTactic    of Names.KerName.t * Tacenv.ltac_entry
  (** Representation of an Ltac tactic definition *)
  | CoqLtac      of Tacexpr.raw_tactic_expr
  (** AST of an LTAC tactic definition *)
  | CoqGenArg    of Genarg.raw_generic_argument
  (** Coq Generic argument, can contain any type *)
  | CoqQualId    of Libnames.qualid
  (** Qualified identifier *)
  | CoqGlobRef   of Names.GlobRef.t
  (** "Global Reference", which is a type that can point to a module, a constant, a variable, a constructor... *)
  | CoqGlobRefExt of Globnames.extended_global_reference
  (** "Extended Global Reference", as they can contain syntactic definitions too *)
  | CoqImplicit  of Impargs.implicits_list
  (** Implicit status for a constant *)
  | CoqProfData  of Profile_tactic.treenode
  (** Ltac Profiler data *)
  | CoqNotation  of Constrexpr.notation
  (** Representation of a notation (usually a string) *)
  | CoqUnparsing of Ppextend.notation_printing_rules * Notation_gram.notation_grammar
  (** Rules for notation printing and some internals  *)
  (* | CoqPhyLoc  of Library.library_location * Names.DirPath.t * string (\* CUnix.physical_path *\) *)
  | CoqGoal      of Constr.t               Serapi_goals.reified_goal Serapi_goals.ser_goals
  (** Goals, with types and terms in Kernel-level representation *)
  | CoqExtGoal   of Constrexpr.constr_expr Serapi_goals.reified_goal Serapi_goals.ser_goals
  (** Goals, with types and terms in user-level, AST representation *)
  | CoqProof     of EConstr.constr list
  (** Proof object: really low-level and likely to be deprecated. *)
  | CoqAssumptions of Serapi_assumptions.t
  (** Structured representation of the assumptions of a constant. *)
  | CoqComments of ((int * int) * string) list list
  (** List of comments in a document, the list will have one element
     for each call to [Add]; note that with the current model, it is
     hard to do better, as a call to [Add] can map to several
     sentences so comments are really mapped to each of those.

     See https://github.com/coq/coq/issues/12413 for updates on
     improved support *)
  | CoqLibObjects of { library_segment : Summary.Interp.frozen Lib.library_segment; path_prefix : Nametab.object_prefix }
  (** Meta-logical Objects in Coq's library / module system *)

(** There are some Coq types that cannot be seralizaled properly, in
   this case, the types can be "opaque", or we will perform some
   manual serialization, such for GADTs.

    In the past generic arguments were such a case, but that has been
   fixed in SerAPI 0.17. Please open an issue or pull request if you
   find such a discrepancy as to document it here.
*)

(******************************************************************************)
(* Printing Sub-Protocol                                                      *)
(******************************************************************************)

(** {3 Printing Options} *)

(** Query output format  *)
type print_format =
  | PpSer
  (** Output in serialized format [usually sexp] *)
  | PpStr
  (** Output a string with a human-friendly representation *)
  | PpTex
  (** Output a TeX expression *)
  | PpCoq
  (** Output a Coq [Pp.t], representation-indepedent document *)
  (* | PpRichpp *)

(** Printing options, not all options are relevant for all printing backends *)
type format_opt =
  { pp_format : print_format  [@default PpSer]
  (** Output format ({e default PpSer}) *)
  ; pp_depth  : int           [@default 0]
  (** Depth  ({e default 0}) *)
  ; pp_elide  : string        [@default "..."]
  (** Elipsis ({e default: "..."}) *)
  ; pp_margin : int           [@default 72]
  (** Margin ({e default: 72}) *)
  }

type print_opt =
  { sid   : Stateid.t [@default Stm.get_current_state ~doc:Stm.(get_doc 0)];
    (** [sid] denotes the {e sentence id} we are querying over, essential information as goals for example will vary. *)
    pp    : format_opt [@default { pp_format = PpSer; pp_depth = 0; pp_elide = "..."; pp_margin = 72 } ];
    (** Printing format of the query, this can be used to select the type of the answer, as for example to show goals in human-form. *)
  }

val gen_pp_obj : Environ.env -> Evd.evar_map -> coq_object -> Pp.t

(******************************************************************************)
(* Parsing Sub-Protocol                                                       *)
(******************************************************************************)

(* no public interface *)

(******************************************************************************)
(* Query Sub-Protocol                                                         *)
(******************************************************************************)

(** {3 Query Sub-Protocol } *)

(** Predicates on the queries. This is at the moment mostly a token functionality *)
type query_pred =
  | Prefix of string
  (** Filter named objects based on the given prefix *)

(** Query options, note the default values that help interactive use, however in mechanized use we
    do not recommend skipping any field *)
type query_opt =
  { preds : query_pred list [@sexp.list];
    (** List of predicates on queries, mostly a placeholder, will allow to add filtering conditions in the future *)
    limit : int option [@sexp.option];
    (** Limit the number of results, should evolve into an API with resume functionality, maybe we adopt LSP conventions here *)
    sid   : Stateid.t [@default Stm.get_current_state ~doc:Stm.(get_doc 0)];
    (** [sid] denotes the {e sentence id} we are querying over, essential information as goals for example will vary. *)
    pp    : format_opt [@default { pp_format = PpSer; pp_depth = 0; pp_elide = "..."; pp_margin = 72 } ];
    (** Printing format of the query, this can be used to select the type of the answer, as for example to show goals in human-form. *)
    route : Feedback.route_id [@default 0];
    (** Legacy/Deprecated STM query method *)
  }

(** Query commands are mostly a tag and some arguments determining the result type.

    {b Important} Note that [Query] won't force execution of a particular state, thus for example if you
    do [(Query ((sid 3)) Goals)] and the sentence [3] wasn't evaluated, then the query will return zero answers.

    We would ideally evolve towards a true query language, likley having [query_cmd] and [coq_object] be typed
    such that query : 'a query -> 'a coq_object.
 *)
type query_cmd =
  | Option
  (** List of options Coq knows about *)
  | Search
  (** Query version of the [Search] command *)
  | Goals                          (* Return goals [TODO: Add filtering/limiting options] *)
  (** Current goals, in kernel form *)
  | EGoals                         (* Return goals [TODO: Add filtering/limiting options] *)
  (** Current goals, in AST form *)
  | Ast                            (* Return ast *)
  (** Ast for the current sentence  *)
  | TypeOf     of string           (* XXX Unimplemented *)
  (** Type of an expression (unimplemented?)  *)
  | Names      of string           (* argument is prefix -> XXX Move to use the prefix predicate *)
  (** [(Names prefix)] will return the list of identifiers Coq knows that start with [prefix]  *)
  | Tactics    of string           (* argument is prefix -> XXX Move to use the prefix predicate *)
  (** [(Tactcis prefix)] will return the list of tactics Coq knows that start with [prefix]  *)
  | Locate     of string           (* argument is prefix -> XXX Move to use the prefix predicate *)
  (** Query version of the [Locate] commands  *)
  | Implicits  of string           (* XXX Print LTAC signatures (with prefix) *)
  (** Return information of implicits for a given constant *)
  | Unparsing  of string           (* XXX  *)
  (** Return internal information for a given notation *)
  | Definition of string
  (** Return the definition for a given global *)
  | LogicalPath of string
  (** Returns Coq's "logical path" for a given file *)
  | PNotations                     (* XXX  *)
  (** Return a list of notations *)
  | ProfileData
  (** Return LTAC profile data, if any *)
  | Proof
  (** Return the proof object [low-level] *)
  | Vernac     of string
  (** Execute an arbitrary Coq command in an isolated state. *)
  | Env
  (** Return the current enviroment *)
  | Assumptions of string
  (** Return the assumptions of a given global *)
  | Complete of string
  (** Naïve but efficient prefix-based completion of identifiers *)
  | Comments
  (** Get all comments of a document *)
  | Objects
  (** Get Coq meta-logical module objects *)

module QueryUtil : sig
  val info_of_id : Environ.env -> string -> coq_object list * coq_object list
end

(******************************************************************************)
(* Control Sub-Protocol                                                       *)
(******************************************************************************)

(** {3 Control Sub-Protocol } *)

(** {4 Adding a new sentence } *)

type parse_entry = Vernac | Constr

(** parse [ontop] of the given sentence with entry [entry] *)
type parse_opt =
  { ontop  : Stateid.t option [@sexp.option]
  ; entry : parse_entry [@default Vernac]
  }

(** [Add] will take a string and parse all the sentences on it, until an error of the end is found.
    Options for [Add] are: *)
type add_opts = {
  lim    : int       option [@sexp.option];
  (** Parse [lim] sentences at most ([None] == no limit) *)
  ontop  : Stateid.t option [@sexp.option];
  (** parse [ontop] of the given sentence *)
  newtip : Stateid.t option [@sexp.option];
  (** Make [newtip] the new sentence id, very useful to avoid synchronous operations *)
  verb   : bool      [@default false];
  (** [verb] internal Coq parameter, be verbose on parsing *)
}

(******************************************************************************)
(* Init / new document                                                        *)
(******************************************************************************)

(** {4 Creating a new document }
    {b experimental} *)

type newdoc_opts =
  { top_name     : Coqargs.top
  (** name of the top-level module of the new document *)
  ; ml_load_path   : string list option [@sexp.option]
  (** Initial ML loadpath  *)
  ; vo_load_path   : Loadpath.vo_path list option [@sexp.option]
  (** Initial LoadPath for the document *) (* [XXX: Use the coq_pkg record?] *)
  ; require_libs : Coqargs.require_injection list option [@sexp.option]
  (** Libraries to load in the initial document state *)
  }

(** Save options, Coq must save a module `Foo` to a concrete module
   path determined by -R / -Q options , so we don't have a lot of
   choice here. *)
type save_opts =
  { prefix_output_dir : string option [@sexp.option]
  (** prefix a directory to the saved vo file. *)
  ; sid : Stateid.t [@default Stm.get_current_state ~doc:Stm.(get_doc 0)]
  (** sid of the point to save the document *)
  }

(******************************************************************************)
(* Help                                                                       *)
(******************************************************************************)

(* no public interface *)

(******************************************************************************)
(* Top-Level Commands                                                         *)
(******************************************************************************)

(** {3 Top Level Protocol }

    The top level protocol is the main input command to SerAPI, we
    detail each of the commands below.

    The main interaction loop is as:
    1. submit tagged command [(tag (Cmd args))]
    2. receive tagged ack [(Answer tag Ack)]
    3. receive tagged results, usually [(Answer tag (ObjList ...)] or [(Answer tag (CoqExn ...)]
    4. receive tagged completion event [(Answer tag Completed)]

    The [Ack] and [Completed] events are always produced, and provide a kind of "bracking" for command execution.

 *)

(** Each top level command will produce an answers, see below for answer description. *)
type cmd =
  | NewDoc     of newdoc_opts
  (** Create a new document, experimental, only usable when [--no_init] was used. *)
  | SaveDoc    of save_opts
  (** Save the .vo file corresponding to the current document, note
     that proofs must be closed etc... in order for this to succeed. *)
  | Add        of add_opts  * string
  (** Add a set of sentences to the current document *)
  | Cancel     of Stateid.t list
  (** Remove a set of sentences from the current document *)
  | Exec       of Stateid.t
  (** Execute a particular sentence *)
  | Query      of query_opt * query_cmd
  (** Query a Coq document *)
  | Print      of print_opt * coq_object
  (** Print some object *)
  | Parse      of parse_opt * string
  (** Parse *)
  | Join
  (** Be sure that a document is consistent *)
  | Finish
  (** Internal *)
  (*******************************************************************)
  (* Non-supported commands, only for convenience.                   *)
  | ReadFile   of string
  | Tokenize   of string
  (*******************************************************************)
  (* Administrativia                                                 *)
  | Noop
  | Help
  (*******************************************************************)

(******************************************************************************)
(* Answer Types                                                               *)
(******************************************************************************)

(** raised when referring to a [Stateid.t] unknown to SerAPI *)
exception NoSuchState of Stateid.t

(** raised when trying to save a module without a corresponding
   [--topfile] *)
exception CannotSaveVo

module ExnInfo : sig
  type t =
    { loc : Loc.t option
    ; stm_ids : (Stateid.t * Stateid.t) option
    ; backtrace : Printexc.raw_backtrace
    ; exn : exn
    ; pp : Pp.t
    ; str : string
    }
end

type answer_kind =
  | Ack
  (** The command was received, Coq is processing it. *)
  | Completed
  (** The command was completed. *)
  | Added     of Stateid.t * Loc.t * Stm.add_focus
  (** A sentence was added, with corresponding sentence id and location. *)
  | Canceled  of Stateid.t list
  (** A set of sentences are not valid anymore. *)
  | ObjList   of coq_object list
  (** Set of objects, usually the answer to a query *)
  | CoqExn    of ExnInfo.t
  (** The command produced an error, optionally at a document location *)

(** {3 State of the evaluator}  *)

module State : sig

  type t

  (** Create a state and possibly initialize Coq with an input_file *)
  val make : ?in_file:string -> ?ldir:Names.DirPath.t -> unit -> t

end

(** {3 Entry points to the DSL evaluator} *)

(** [exec_cmd cmd] execute SerAPI command *)
val exec_cmd : State.t -> cmd -> answer_kind list * State.t

(** Each command and answer are tagged by a user-provided identifier *)
type cmd_tag = string
type tagged_cmd = cmd_tag * cmd

(** We introduce our own feedback type to overcome some limitations of
   Coq's Feedback, for now we only modify the Message data *)

type feedback_content =
  | Processed
  | Incomplete
  | Complete
  | ProcessingIn of string
  | InProgress of int
  | WorkerStatus of string * string
  | AddedAxiom
  | FileDependency of string option * string
  | FileLoaded of string * string
  | Message of { level: Feedback.level ; loc : Loc.t option ; pp : Pp.t ; str: string }

type feedback =
  { doc_id   : Feedback.doc_id
  ; span_id  : Stateid.t
  ; route    : Feedback.route_id
  ; contents : feedback_content
  }

(** General answers of the protocol can be responses to commands, or
   Coq messages *)
type answer =
  | Answer    of cmd_tag * answer_kind
  (** The answer is comming from a user-issued command *)
  | Feedback  of feedback
  (** Output produced by Coq (asynchronously) *)
