(** Define the global configuration options *)

(** {1 Backend choice} *)

(** The choice of backend *)
type backend = FStar | Coq | Lean | HOL4 [@@deriving show]

let backend_names = [ "fstar"; "coq"; "rocq"; "lean"; "hol4" ]

(** Utility to compute the backend from an input parameter *)
let backend_of_string (b : string) : backend option =
  match b with
  | "fstar" | "FStar" -> Some FStar
  | "coq" | "Coq" | "rocq" | "Rocq" -> Some Coq
  | "lean" | "Lean" -> Some Lean
  | "hol4" | "HOL4" -> Some HOL4
  | _ -> None

let opt_backend : backend option ref = ref None

let set_backend (b : string) : unit =
  match backend_of_string b with
  | Some b -> opt_backend := Some b
  | None ->
      (* We shouldn't get there: the string should have been checked as
         belonging to the proper set *)
      raise (Failure "Unexpected")

(** Specify the namespace of the extract code.

    For instance, if the crate name is [foo] the namespace used for the
    extracted code will be [foo] but the user might want to use [Foo] instead.
*)
let namespace : string option ref = ref None

let set_namespace (s : string) : unit = namespace := Some s

(** Place the files inside a subdirectory in the destination.

    We use this to properly generate the import paths.

    For instance, when generating files for Lean, if the user wants to extract
    the files in the subdir [Foo/Code], the imports will have to be prefixed
    with [Foo.Code] (e.g., [import Foo.Code.Types]). *)
let subdir : string option ref = ref None

let set_subdir (s : string) : unit = subdir := Some s

(** If [true], we do not generate code and simply borrow-check the program
    instead. This allows us to relax some sanity checks which are present in the
    symbolic execution only to make sure we will be able to generate the pure
    translation.

    Remark: when checking if we are borrow-checking a program, checking this
    boolean or checking if [opt_backend] is [None] are equivalent. We need to
    have different variables for the purpose of implementing the parsing of the
    CI arguments. *)
let borrow_check = ref false

(** Get the target backend

    If there is no backend (we are borrow-checking) we default to Lean - it
    happens when looking up the builtin information: we use Lean as it has the
    most complete library.

    TODO: turn borrow-checking into a backend. *)
let backend () : backend =
  match !opt_backend with
  | None -> Lean
  | Some b -> b

let backend_to_string (b : backend) =
  match b with
  | FStar -> "F*"
  | Coq -> "Rocq"
  | Lean -> "Lean"
  | HOL4 -> "HOL4"

let backend_name () : string = backend_to_string (backend ())

let if_backend (f : unit -> 'a) (default : 'a) : 'a =
  match !opt_backend with
  | None -> default
  | Some _ -> f ()

(** Print the source code span which emitted errors *)
let print_error_emitters = ref false

(** Print all the external definitions which are not listed in the builtin
    functions *)
let print_unknown_externals = ref false

(** {1 Interpreter} *)

(** Activate the sanity checks, and in particular the invariant checks that are
    performed at every evaluation step. This is very expensive (~100x slow down)
    but very efficient to catch mistakes early. *)
let sanity_checks = ref false

(** Expand all symbolic values containing borrows upon introduction - allows to
    use restrict ourselves to a simpler model for the projectors over symbolic
    values. The interpreter fails if doing this requires to do a branching
    (because we need to expand an enumeration with strictly more than one
    variant) or if we need to expand a recursive type (because this leads to
    looping). *)
let greedy_expand_symbolics_with_borrows = true

(** Experimental.

    TODO: remove (always true now), but check that when we panic/call a function
    there is no bottom below a borrow.

    We use this in two situations:

    1. We sometimes want to temporarily break the invariant that there is no
    bottom value below a *mutable* borrow. If this value is true, we don't check
    the invariant, and the rule becomes: we can't end a borrow *if* it contains
    a bottom value. The consequence is that it becomes ok to temporarily have
    bottom below a borrow, if we put something else inside before ending the
    borrow.

    For instance, when evaluating an assignment, we move the value which will be
    overwritten then do some administrative tasks with the borrows, then move
    the rvalue to its destination. We currently want to be able to check the
    invariants every time we end a borrow/an abstraction, meaning at
    intermediate steps of the assignment where the invariants might actually be
    broken.

    2. We sometimes need to join a value containing loans with a value
    containing bottoms. For instance, when joining:
    {[
      v -> bottom   U   v -> SL l 0
    ]}

    A problem is that we can't move [SL l 0] to a region abstraction or an
    anonymous values, because it is an **outer** loan: doing so would allow the
    loan to live indefinitely, and in particuler we would be allowed to
    overwrite [v] without ending it.

    A possibility is to force [l] to end, but then it might lead to a borrow
    checking issue later on, when trying to use the borrow [l]. Our solution is
    to use a shared loan containing the value bottom, leading to the following
    environment:

    {[
      v -> SL l' bottom
      abs { SB l', SL l 0 }
    ]}

    This way, the borrow [l] is preserved, but upon overwriting [v] we have to
    en [l'], which in turns requires ending [l]. We also can't *read* from [v],
    because after we ended the loan, [v] maps to [bottom] (we can only write to
    it). Also note that the shared borrow [l'] can't be used in any way (in
    particular, it can't be dereferenced).

    Finally, this solution works for mutable borrows/loans:
    {[
      v -> bottom   U   v -> ML l

        ~>

      v -> SL l' bottom
      abs { SB l', ML l }
    ]} *)
let allow_bottom_below_borrow = true

(** If a function doesn't return any borrows, we can immediately call its
    backward functions. If this option is on, whenever we call a function *and*
    this function returns unit, we immediately end all the abstractions which
    are introduced and don't contain loans. This can be useful to make the code
    cleaner (the backward function is introduced where the function call
    happened) and make sure all forward functions with no return value are
    followed by a backward function. *)
let return_unit_end_abs_with_no_loans = true

(** The maximum number of iterations we can do to find a loop fixed point.

    This is mostly for sanity: we should always find a fixed point in a
    reasonable number of iterations. If we fail to do so, it is likely a bug: we
    thus use this bound to detect a loop, fail and report the case to the user.
*)
let loop_fixed_point_max_num_iters = 2

(** {1 Translation} *)

(** Forbids using field projectors for structures.

    If we don't use field projectors, whenever we symbolically expand a
    structure value (note that accessing a structure field in the symbolic
    execution triggers its expansion), then instead of generating code like
    this:
    {[
      let x1 = s.f1 in
      let x2 = s.f2 in
      ...
    ]}

    we generate code like this:
    {[
      let Mkstruct x1 x2 ... = s in
      ...
    ]}

    Rem.: this used to be useful for Coq, because in Coq we can't define groups
    of mutually recursive records and inductives. In such cases, we extract the
    structures as inductives, which means that field projectors are not always
    available. As of today, we generate field projectors definitions (together
    with the appropriate notations). *)
let dont_use_field_projectors = ref false

(** Deconstructing ADTs which have only one variant with let-bindings is not
    always supported: this parameter controls whether we use let-bindings in
    such situations or not. *)
let always_deconstruct_adts_with_matches = ref false

(** Controls whether we use fuel to control termination. *)
let use_fuel = ref false

(** Controls whether we split the generated definitions between different files
    for the types, clauses and functions, or if we group them in one file. *)
let split_files = ref false

(** Only for Lean: generate the library entry point, if the crate is split
    between different files. The entry point is simply a file with the name of
    the crate and which includes all the other files. *)
let generate_lib_entry_point = ref false

(** For Lean, controls whether we generate a lakefile or not. *)
let lean_gen_lakefile = ref false

(** If true, treat the unit functions (function taking no inputs and returning
    no outputs) as unit tests: evaluate them with the interpreter and check that
    they don't panic. *)
let test_unit_functions = ref false

(** If [true], use decreases clauses/termination measures for all the recursive
    definitions.

    More precisely:
    - for F*, we generate definitions which use decreases clauses
    - for Lean, we generate definitions which use termination measures and
      decreases proofs

    The body of such clauses/proofs must be defined by the user. *)
let extract_decreases_clauses = ref false

(** In order to help the user, we can generate "template" decrease clauses/
    termination measures (i.e., definitions with proper signatures but dummy
    bodies) in a dedicated file.

    We initialize it to [true], then deactivate it depending on the CL options
    given by the user. *)
let extract_template_decreases_clauses = ref true

(** {1 Micro passes} *)

(** Some provers like F* and Coq don't support the decomposition of return
    values in monadic let-bindings:
    {[
      (* NOT supported in F*/Coq *)
      (x, y) <-- f ();
      ...
    ]}

    In such situations, we might want to introduce an intermediate assignment:
    {[
      tmp <-- f ();
      let (x, y) = tmp in
      ...
    ]} *)
let decompose_monadic_let_bindings = ref false

(** Some provers like Coq don't support nested patterns in let-bindings:
    {[
      (* NOT supported in Coq *)
      (st, (x1, x2)) <-- f ();
      ...
    ]}

    In such situations, we might want to introduce intermediate assignments:
    {[
      (st, tmp) <-- f ();
      let (x1, x2) = tmp in
      ...
    ]} *)
let decompose_nested_let_patterns = ref false

(** Controls the unfolding of monadic let-bindings to explicit matches:

    [y <-- f x; ...]

    becomes:

    [match f x with | Failure -> Failure | Return y -> ...]

    This is useful when extracting to F*: the support for monadic definitions is
    not super powerful. Note that when {!unfold_monadic_let_bindings} is true,
    setting {!decompose_monadic_let_bindings} to true and only makes the code
    more verbose. *)
let unfold_monadic_let_bindings = ref false

(** Perform the following transformation:

    {[
      let y <-- f x   (* Must be an application, is not necessarily monadic *)
      let (a, b) := y (* Tuple decomposition *)
    ]}

    becomes:

    {[
      let (a, b) <-- f x
    ]} *)
let merge_let_app_decompose_tuple = ref false

(** Perform the following transformation:

    {[
      let y <-- ok e

            ~~>

      let y <-- toResult e
    ]}

    We only do this on a specific set of pure functions calls - those functions
    are identified in the "builtin" information about external function calls.
*)
let lift_pure_function_calls = ref false

(** Introduce calls to [massert] (monadic assertion).

    The pattern below is very frequent especially as it is introduced by the
    [assert!] macro. If the option is [true], we perform the following
    simplification:
    {[
      if b then e else fail ~~>massert b;
      e
    ]} *)
let intro_massert = ref true

(** Simplify the forward/backward functions, in case we merge them (i.e., the
    forward functions return the backward functions).

    The simplification occurs as follows:
    - if a forward function returns the unit type and has non-trivial backward
      functions, then we remove the returned output.
    - if a backward function doesn't have inputs, we evaluate it inside the
      forward function and don't wrap it in a result.

    Example:
    {[
      // LLBC:
      fn incr(x: &mut u32) { *x += 1 }

      // Translation without simplification:
      let incr (x : u32) : result (unit * result u32) = ...
                                   ^^^^   ^^^^^^
                                    |     remove this result
                                remove the unit

      // Translation with simplification:
      let incr (x : u32) : result u32 = ...
    ]} *)
let simplify_merged_fwd_backs = ref true

(** Use short names for the record fields.

    Some backends can't disambiguate records when their field names have
    collisions. When this happens, we use long names, by which we concatenate
    the record names with the field names, and check whether there are name
    collisions.

    For backends which can disambiguate records (typically by using the typing
    information), we use short names (i.e., the original field names). *)
let record_fields_short_names = ref false

(** Parameterize the traits with their associated types, so as not to use types
    as first class objects.

    This is useful for some backends with limited expressiveness like HOL4, and
    to account for type constraints (like
    [fn f<T : Foo>(...) where T::bar = usize]). *)
let parameterize_trait_types = ref false

(** For sanity check: type check the generated pure code (activates checks in
    several places).

    TODO: fix the bugs and reactivate *)
let type_check_pure_code = ref false

(** Shall we fail hard if we encounter an issue, or should we attempt to go as
    far as possible while leaving "holes" in the generated code? *)
let fail_hard = ref false

(** Shall we emit errors instead of warnings? *)
let warnings_as_errors = ref false

(** If true, add the type name as a prefix to the variant names. Ex.: In Rust:
    {[
      enum List = {
        Cons(u32, Box<List>),x
        Nil,
      }
    ]}

    F*, if option activated:
    {[
      type list =
      | ListCons : u32 -> list -> list
      | ListNil : list
    ]}

    F*, if option not activated:
    {[
      type list =
      | Cons : u32 -> list -> list
      | Nil : list
    ]} *)
let variant_concatenate_type_name = ref true

(** If true, extract the structures with unnamed fields as tuples.

    ex.:
    {[
      // Rust
      struct Foo(u32, u32)

      // OCaml
      type Foo = u32 * u32
    ]} *)
let use_tuple_structs = ref true

let backend_has_tuple_projectors backend =
  match backend with
  | Lean -> true
  | Coq | FStar | HOL4 -> false

(** Toggle the use of tuple projectors *)
let use_tuple_projectors = ref false

(** We we use nested projectors for tuple (like: [(0, 1).snd.fst]) or do we use
    better projector syntax? *)
let use_nested_tuple_projectors = ref false

(** Generate name patterns for the external definitions we encounter *)
let extract_external_name_patterns = ref true

(** *)
let match_patterns_with_trait_decl_refs = true

(** Always decompose loops to recursive functions *)
let loops_to_recursive_functions = ref false

(** Should we run the translation in parallel?

    Note: the race condition on Pack.Digraph's global vertex counter in SCC.ml
    has been fixed by switching to Imperative.Digraph.Concrete, and the pool is
    now persistent (created once and reused).

    Note: the way functions are ordered before being translated is wrong:
    - the function which computes the size of the function should count the the
      loops differently (the body of a loop is executed twice to compute a fixed
      point: the result is exponential)
    - the way the parellelism is executed implies that the first domain will
      translate all the biggest functions! We should rather have a queue of
      tasks (or an index of the next function to translate that we would
      atomically increment)
    - it is probably worth reordering the functions also before running the
      micro-passes *)
let parallel = ref true

(** Once we add proper support for static lifetimes, remove this *)
let use_static = ref false

(** Display a progress bar *)
let progress_bar = ref true

(** For debugging: when we error on an external definition, we display the list
    spans where it is transitively used in the local crate. This is the maximum
    number of spans we print (a negative number means we print all of them) *)
let max_error_spans = ref 5

(** If the join after a match/switch/etc. fails we make it recoverable: instead
    of raising an error we do not join the contexts and duplicate the code after
    the match/switch/etc. *)
let recover_joins = ref true

(** When analyzing types, for instance to check whether they use erased regions
    or not, we ignore dynamic traits.

    This may cause issues in the future once we want to be more general: for
    this reason we guard all checks with [type_analysis_ignore_dyn] so that it
    is easy to activate them. *)
let type_analysis_ignore_dyn = true

(** We currently incorrectly use the region inside the dyn trait: once we update
    the use, remove this boolean: this will reveal important places that need to
    be updated. *)
let use_dyn_regions = false

(** When analyzing an opaque type about which we have no information, should we
    consider its regions as being used for mutable references or not? *)
let opaque_types_have_mut_regions_by_default = false

(** Should we use colors when logging? *)
let log_with_colors = ref false

(** Should we use rotating colors when loggin (i.e., rather than using a color
    per category of item, such as borrows, loans, etc. use a color based on the
    index of the item: this allows easily identifying a borrow and its
    corresponding loan) *)
let log_rotating_colors = ref true

(** {Diagnostics} *)

(** If activated, measure the time it takes to translate every function (through
    [Translate.translate_function_to_pure]) and print the results sorted from
    longest to shortest, together with the function size. *)
let diagnose_translation = ref false

(** If activated, measure the time it takes to apply the micro-passes on every
    function, and print them from the longest to the shortest, together with the
    function size. *)
let diagnose_micro_passes = ref false

(** If activated in combination with -diagnose-micro-passes, compute
    per-function, per -micro-pass time measurements. *)
let diagnose_detailed = ref false

(** Upper bound on the number of lines printed for the diagnose options. If
    positive, print at most this many lines. If negative, print everything. *)
let diagnose_limit = ref (-1)

(** Should we borrow check globals?

    The issue is that when translating a global which uses a 'static reference,
    the LLBC provided by Charon for the body of the global (which initializes
    the constant) is too simplified and essentially looks like this:
    {[
      fn initialize() -> &'static u32 {
        let x = 0;
        &x // reference to local variable!
      }
    ]}

    In order to translate these globals we deactivate the invalidation of local
    variables upon return in these initialization functions. This means that we
    do not borrow-check these initialization functions, but the generated pure
    model should still be fine. *)
let borrow_check_globals = ref false

(** *)
let print_error_diagnostics = ref false

(** There can be collisions between method names and projector names.

    For instance:

    {[
      struct Struct { len : usize }

      impl Struct {
          // If we name this Struct.len in Lean there will be a name collision
          // with the projector function for field len
          fn len(&self) -> usize { self.len }
      }
    ]}
    By default, we detect such collisions and change the method name accordingly
    (in the case above, the method [len] would be named [Struct.impl.len] in
    Lean instead of [Struct.impl.len]).

    One issue is that it makes the name generation non-modular and introduces
    inconsistencies between method names, depending on whether there exists a
    field with the same name or not.

    If the following option is on, we introduce the [impl] name elemnt in *all*
    method names. *)
let method_names_in_impl_namespace = ref false

(** *)
let all_computable = ref false

(** Do not attempt to extract loops to recursive functions *)
let no_recursive_loops = ref false

(** This is for Lean: the value we should initialize `maxHeartBeats` to at the
    top of the generated files *)
let max_heartbeats = ref 1000000

(** This is for Lean: the value we should initialize `maxRecDepth` to at the top
    of the generated files *)
let max_recdepth = ref 2048

(** If [false], evaluate [drop(p)] as [p := bottom]. Otherwise, evaluate it as a
    no-op (which means that we do not borrow-check the drops). *)
let drop_as_no_op = ref true
