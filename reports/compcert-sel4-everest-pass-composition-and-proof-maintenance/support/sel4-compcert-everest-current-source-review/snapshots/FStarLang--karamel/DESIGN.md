Overview of KaRaMeL
-------------------

From a high-level perspective, KaRaMeL takes an input AST, translates it into a
typed internal AST, then massages the program by performing repeated
transformations until the program fits within a simple enough subset dubbed
Low\*. Once a program is valid Low\*, it translates almost trivially into C\*, an
idealized dialect of C. Then, the program is translated to an abstract C AST,
and finally pretty-printed.

The detailed steps are as follows. KaRaMeL:
- loads an AST written by F\* or Dafny (see `InputAst.ml`)
- translates it into an AST where expressions and patterns are annotated with
  their types (see `InputAstToAst.ml`, `Ast.ml`)
- re-checks the program to see that it makes sense; possibly drops some
  ill-typed bits (see `Checker.ml`)
- substitutes parameterized type abbreviations with their expansion (see
  `Inlining.ml`); at this stage, all `DType (Abbrev, ...)` have zero parameters;
- performs a whole-program monomorphization of data types (`Variant`, `Flat`);
  at this stage, every single `DType` has zero parameters (see `DataTypes.ml`)
  and `TBound` and `TApp` are gone;
- removes tuples in favor of ad-hoc, monomorphic declarations; `TTuple`,
  `ETuple` and `PTuple` nodes are gone;
- removes dummy matches on booleans and units;
- simplifies data types (see `DataTypes.ml`):
  * data types with only constant constructors are translated to `Enum`
    declarations and `ESwitch` expressions; `DType (Enum, ...)`, `ESwitch`,
    `EEnum` and `TEnum` start appearing in the AST;
  * data types with a single branch are simplified into a `DType (Flat, ...)`
    and `EMatch` nodes for such data types are turned into a series of bindings
  * other data types are turned into a tagged enum; `TAnonymous` nodes may
    appear, possibly containing `Union` and `Struct` type declarations; `EMatch`
    expressions for such data types are turned into a series of conditionals and
    bindings; `DType (Variant, ...)` nodes are gone; `ECons`, `PCons` nodes are
    gone;
  * at this stage, all `EMatch` expressions are gone;
- performs a round of transformations (see `src/Simplify.ml`), namely:
  * turns global names into valid C identifiers;
  * eta-expands toplevel definitions (e.g. `let f = g`);
  * inserts proper casts to get wraparound semantics for signed arithmetic
    operations;
  * goes from an expression language to a statement language, by hoisting all
    expressions that are not C expressions into statements and/or assignments;
- inlines all functions that are determined to be in the `StackInline` effect,
  using a conservative syntactic criterion (see `Inlining.ml`);
- performs part of the "round of transformations" again (‡).

At this stage, the (unverified) invariant is that the any program fits the
definition of Low\* and can be trivially translated to C\*; KaRaMeL then:
- translates the program to C* (see `CStar.ml`, `AstToCStar.ml`); this involves
  * going from a lexical scope to a block scope while preserving names insofar
    as possible;
  * optimizing functions that return unit into functions that return void;
  * optimizing functions that take unit into functions that take no parameters;
- groups files according to the `-bundle` arguments;
- drops files according to the `-drop` arguments;
- translates the C* program to an abstract C syntax tree (see `C.ml`,
  `CStarToC.ml`); this involves:
  * turning ML-style types into specifiers and declarators;
  * replacing all high-level nodes with actual C constructs;
  * making the initialization of buffers explicit;
- prints the C abstract tree into actual syntax (see `PrintC.ml`); this
  involves:
  * respecting the precedence of operators;
  * dealing with C ambiguities (e.g. dangling else)
  * introducing sensible indentation.

WASM Backend
------------

This is an alternative code generation pipeline that branches off at (‡), i.e.
after the "round of transformations".

This codepath is conditional on the `-wasm` flag; KaRaMeL then:
- desugars some more high-level constructs (e.g. creation of a buffer with an
  initial value, buffer blitting) into a series of loops and assignments --
  these were only kept to generate more idiomatic C code;
- removes struct-returning functions (20170210: currently a todo) in favor of
  unit-returning functions that take an extra pointer to a caller-allocated
  struct;
- translates to Cflat, a language where all local variables have been
  pre-allocated in the current function's stack frame, and where the only two
  sizes left are I32 and I64 (we keep exact width information to generate
  correct code for arithmetic computations, though);
- translates to Wasm, generating a Wasm module for each (possibly-bundled) F\*
  module.
