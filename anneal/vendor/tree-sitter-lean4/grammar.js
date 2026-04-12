/**
 * @file Lean 4 grammar for tree-sitter
 * @license MIT
 *
 * Based on best practices from tree-sitter-javascript and tree-sitter-rust
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

// Centralized precedence levels (higher = binds tighter)
// Based on Lean 4's actual precedence: https://leanprover.github.io/lean4/doc/operators.html
const PREC = {
  // Expression precedences (6 binary levels + unary/app/proj/atom)
  low: 25,          // $ || ∨ (merged: or + $)
  and: 35,          // &&
  compare: 40,      // == != < > <= >=
  add: 55,          // + - ++ :: × (merged: cons + add + product)
  mul: 60,          // * / %
  unary: 70,        // ! ¬ -
  app: 80,          // function application
  proj: 90,         // .field
  atom: 100,        // literals, identifiers
};

// Helper functions
function commaSep1(rule) {
  return seq(rule, repeat(seq(',', rule)));
}

function commaSep(rule) {
  return optional(commaSep1(rule));
}

module.exports = grammar({
  name: 'lean',

  extras: $ => [
    $.comment,
    /\s/,
  ],

  // External scanner for layout-sensitive constructs (indentation-based parsing)
  externals: $ => [
    $._layout_start,      // Start a layout block (after `do`, `where`, etc.)
    $._layout_semicolon,  // Virtual semicolon between elements at same indent
    $._layout_end,        // End of layout block (indent decreased)
    $._match_body_start,  // Like _layout_start but only for match arm bodies
  ],

  // Keyword extraction improves error detection and compile time
  word: $ => $.identifier,

  // Supertype nodes for better queries
  supertypes: $ => [
    $._expression,
    $._declaration,
  ],

  // Inline rules to reduce tree depth
  inline: $ => [],

  conflicts: $ => [
    [$.where_decl],
    [$.subtype, $.field_assignment],
    [$.let, $._pattern],
    [$.parameters, $._pattern],
  ],

  rules: {
    // ============================================================
    // Module Structure
    // ============================================================

    module: $ => seq(
      optional($.prelude),
      repeat($.import),
      repeat($._command),
    ),

    prelude: _ => 'prelude',

    // Import: `import Lean.Data.Json`
    // Module path is parsed as identifier or projection chain
    import: $ => seq('import', field('module', $._expression)),

    // ============================================================
    // Commands
    // ============================================================

    _command: $ => choice(
      // Declarations, notations, and examples with optional leading modifiers
      seq(repeat($._modifier), choice(
        $._declaration, $.declaration, $.example,
        $.notation, $.attribute,
      )),
      // Other commands (no modifiers)
      $.namespace,
      $.section,
      $.end,
      $.open,
      $.export,
      $.variable,
      $.universe,
      $.hash_command,
    ),

    // Modifier keywords consumed transparently (no node created)
    _modifier: _ => choice('noncomputable', 'partial', 'protected', 'private', 'unsafe', 'scoped', 'local'),


    // Namespace: `namespace Foo` or `namespace Foo.Bar.Baz`
    namespace: $ => seq('namespace', field('name', $._name)),

    section: $ => seq('section', optional(field('name', $._name))),

    // End: `end` or `end Foo` or `end Foo.Bar.Baz`
    end: $ => seq('end', optional(field('name', $._name))),

    // Open: `open Foo.Bar` or `open Foo Bar Baz` or `open Foo hiding x` or `open Foo (x y)`
    open: $ => seq(
      'open',
      optional('scoped'),
      repeat1(field('namespace', $._name)),
      optional(choice(
        seq('hiding', repeat1(field('hiding', $._name))),
        seq('(', repeat1(field('only', $._name)), ')'),
        seq('in', $._command),
      )),
    ),

    // `export Foo (bar baz)`
    export: $ => seq(
      'export',
      field('class', $.identifier),
      '(', repeat($.identifier), ')',
    ),

    variable: $ => seq('variable', repeat1($._bracketed_binder)),

    universe: $ => seq(choice('universe', 'universes'), repeat1($.identifier)),

    // `attribute [simp] Nat.add_zero`
    attribute: $ => prec.left(seq(
      'attribute',
      '[', commaSep1($.identifier), ']',
      repeat1($._expression),
    )),

    // `notation:10000 n "!" => factorial n`
    notation: $ => prec.left(seq(
      choice('notation', 'macro_rules', 'syntax', 'macro', 'elab',
             'prefix', 'infix', 'infixl', 'infixr', 'postfix'),
      optional(seq(':', $.number)),  // priority
      repeat(choice($._expression, '=>', ':=')),
    )),

    // `#check`, `#eval`, `#print`, etc.
    hash_command: $ => prec.left(seq(
      /#[a-zA-Z_]\w*/,
      repeat($._expression),
    )),

    // `example : 1 + 1 = 2 := by rfl`
    example: $ => seq(
      'example',
      optional(field('binders', $.binders)),
      optional($._type_spec),
      ':=',
      field('body', $._expression),
    ),

    // ============================================================
    // Declarations
    // ============================================================

    _declaration: $ => choice(
      $.definition,
      alias($._instance_decl, $.definition),
      $.constant,
      $.opaque,
      $.axiom,
      $.structure,
      $.inductive,
      $.class_inductive,
    ),

    // `@[simp] def f := 12` — declaration with leading attributes
    declaration: $ => seq(
      field('attributes', $.attributes),
      repeat($._modifier),
      $._declaration,
    ),

    // `@[simp, inline]` or `@[extern "foo"]`
    attributes: $ => seq(
      '@', '[',
      repeat1(choice(
        seq('extern', field('extern', $.string)),
        field('name', $._name),
        ',',
      )),
      ']',
    ),

    // def/theorem/lemma/abbrev — name is required, no ambiguity with binders.
    // Modifiers (noncomputable, partial, etc.) are consumed transparently.
    definition: $ => seq(
      field('kind', choice('def', 'theorem', 'lemma', 'abbrev')),
      field('name', $._name),
      optional(field('binders', $.binders)),
      optional($._type_spec),
      $._declaration_body,
    ),

    // Shared body production for definition and instance — factored out
    // to let the parser reuse states across both declaration forms.
    _declaration_body: $ => choice(
      seq(':=', $._layout_start, field('body', $._expression), optional($._layout_end)),
      seq('where', $._layout_start, repeat1(seq(field('body', $.where_decl), optional($._layout_semicolon))), optional($._layout_end)),
      repeat1($.match_arm),
    ),

    // instance — name is optional; aliased to `definition` in the parse tree.
    // Instance binders are always bracketed (no bare identifier ambiguity with name).
    _instance_decl: $ => seq(
      'instance',
      optional(field('name', $.identifier)),
      repeat(field('binders', $._bracketed_binder)),
      optional($._type_spec),
      $._declaration_body,
    ),

    // A single method/field definition inside a `where` block
    where_decl: $ => seq(
      field('name', $.identifier),
      repeat(field('binders', choice($.identifier, $._bracketed_binder))),
      optional($._type_spec),
      ':=',
      $._layout_start,
      field('body', $._expression),
      optional($._layout_end),
    ),

    // `constant foo : T` — opaque constant declaration
    constant: $ => seq(
      'constant',
      field('name', $._name),
      optional($._type_spec),
      optional(seq(':=', field('body', $._expression))),
    ),

    // `opaque foo : T := e` — opaque definition
    opaque: $ => seq(
      'opaque',
      field('name', $._name),
      optional(field('binders', $.binders)),
      optional($._type_spec),
      optional(seq(':=', field('body', $._expression))),
    ),

    // `axiom foo : T` — axiomatic declaration
    axiom: $ => seq(
      'axiom',
      field('name', $._name),
      $._type_spec,
    ),

    structure: $ => seq(
      choice('structure', 'class'),
      field('name', $.identifier),
      optional(field('binders', $.binders)),
      optional(field('extends', seq('extends', commaSep1($._expression)))),
      optional($._type_spec),
      optional(seq(
        choice(':=', 'where'),
        $._layout_start,
        repeat(seq(field('fields', choice($.structure_field, $._bracketed_binder)), optional($._layout_semicolon))),
        optional($._layout_end),
      )),
      optional(seq('deriving', commaSep1(field('deriving', $.identifier)))),
    ),

    // Structure fields: `x : T` or `x : T := default` or `x := default`
    structure_field: $ => seq(
      field('name', $.identifier),
      repeat($._bracketed_binder),
      choice(
        seq(':', field('type', $._expression), optional(seq(':=', field('default', $._expression)))),
        seq(':=', field('default', $._expression)),
      ),
    ),

    inductive: $ => seq(
      'inductive',
      field('name', $.identifier),
      optional(field('binders', $.binders)),
      optional($._type_spec),
      optional(choice(':=', 'where')),
      repeat(field('constructors', $.constructor)),
      optional(seq('deriving', commaSep1(field('deriving', $.identifier)))),
    ),

    // `class inductive Foo where | ...` — prec(1) to win over `structure`
    // when parser sees `class` followed by `inductive`
    class_inductive: $ => prec(1, seq(
      'class', 'inductive',
      field('name', $.identifier),
      optional(field('binders', $.binders)),
      optional($._type_spec),
      optional(choice(':=', 'where')),
      repeat(field('constructors', $.constructor)),
      optional(seq('deriving', commaSep1(field('deriving', $.identifier)))),
    )),

    constructor: $ => seq(
      '|',
      field('name', $._name),
      optional(field('binders', $.binders)),
      optional($._type_spec),
    ),

    // ============================================================
    // Binders
    // ============================================================

    binders: $ => repeat1(choice($.identifier, $._bracketed_binder)),

    // Quantifier binders: `x y : Nat` or `(x : Nat) {y : Nat}`
    // Bare identifiers can have a trailing `: Type` annotation
    _quantifier_binders: $ => seq(
      repeat1(choice($.identifier, $._bracketed_binder)),
      optional($._type_spec),
    ),

    _bracketed_binder: $ => choice(
      $.explicit_binder,
      $.implicit_binder,
      $.instance_binder,
    ),

    explicit_binder: $ => seq(
      '(',
      repeat1(field('name', $.identifier)),
      optional($._type_spec),
      optional(seq(':=', field('default', $._expression))),
      ')',
    ),

    implicit_binder: $ => seq(
      '{',
      repeat1(field('name', $.identifier)),
      optional($._type_spec),
      '}',
    ),

    instance_binder: $ => seq(
      '[',
      optional(seq(field('name', $.identifier), ':')),
      field('type', $._expression),
      ']',
    ),

    _type_spec: $ => seq(':', field('type', $._expression)),

    // ============================================================
    // Expressions
    // ============================================================

    _expression: $ => choice(
      $._atom,
      $.application,
      $.subscript,
      $.binary_expression,
      $.unary_expression,
      $.explicit,
      // postfix ! and ? are handled by subscript modifier and notation
      $.projection,
      $.arrow,
      $.fun,
      $.quantifier,
      $.let,
      $.have,
      $.if,
      $.if_let,
      $.match,
      $.do,
      $.by,
    ),

    // Atoms: self-delimiting expressions that can appear as function arguments
    _atom: $ => choice(
      $.identifier,
      $.escaped_identifier,
      $.number,
      $.float,
      $.string,
      $.char,
      $.parenthesized,
      $.named_argument,
      $.tuple,
      $.anonymous_constructor,
      $.structure_instance,
      $.array,
      $.list,
      $.range,
      $.hole,
      $.synthetic_hole,
      $.quoted_name,
      $.double_quoted_name,
      $.ellipsis,
      $.sorry,
      $._boolean,
      $.cdot,
      $.subtype,
    ),

    // Function application: `f x y z`
    // Uses prec.left to parse `f x y` as `(f x) y`
    application: $ => prec.left(PREC.app, seq(
      field('name', $._expression),
      field('arguments', choice(
        $._atom,
        $.fun,
        $.if,
        $.match,
        $.do,
        $.by,
      )),
    )),

    // Array/list subscript: `arr[i]` or `arr[i]!` or `arr[i]?`
    // Also handles subarray slice: `arr[start:stop]`
    subscript: $ => prec.left(PREC.proj, seq(
      field('object', $._expression),
      token.immediate('['),
      optional(field('index', $._expression)),
      optional(seq(':', optional(field('stop', $._expression)))),
      ']',
      optional(field('modifier', choice('!', '?'))),
    )),

    // Qualified name: `foo` or `Foo.Bar.baz` - used for declarations and references
    _name: $ => seq(
      choice($.identifier, $.escaped_identifier),
      repeat(seq(token.immediate('.'), choice($.identifier, $.escaped_identifier))),
    ),

    // Projection: `x.foo` or `x.1` or `x.«name»` or `.field` (leading dot)
    projection: $ => prec.left(PREC.proj, seq(
      optional(field('term', $._expression)),
      choice(
        token.immediate('.'),  // For `x.field` where x is an expression
        '.',                   // For `.field` (leading dot)
      ),
      field('name', choice($.identifier, $.escaped_identifier, $.number)),
    )),

    // Arrow type: `A → B`
    arrow: $ => prec.right(PREC.low, seq(
      field('domain', $._expression),
      choice('->', '→'),
      field('codomain', $._expression),
    )),

    // Binary operators with table-driven precedence
    binary_expression: $ => {
      // 6 levels (reduced from 9) to minimize parser states.
      // Merged: or+$ → low, cons+add+product → add.
      const leftAssoc = [
        [PREC.low, choice('||', '∨', '<|>')],
        [PREC.and, choice('&&', '∧')],
        [PREC.compare, choice('==', '!=', '=', '<', '>', '<=', '>=', '≤', '≥', '≠',
                               '∣', '↔', '⊢')],
        [PREC.add, choice('+', '-', '++', '∪', '∩', '×')],
        [PREC.mul, choice('*', '/', '%')],
        [PREC.app + 1, choice('|>', '|>.')],
      ];

      // Right-associative: $, <|, ::, ^, ∘
      const rightAssoc = [
        [PREC.low, '$'],
        [PREC.add, '::'],
        [PREC.mul, choice('^', '∘')],
        [PREC.app + 1, '<|'],
      ];

      return choice(
        ...leftAssoc.map(([precedence, operator]) =>
          prec.left(precedence, seq(
            field('left', $._expression),
            field('operator', operator),
            field('right', $._expression),
          )),
        ),
        ...rightAssoc.map(([precedence, operator]) =>
          prec.right(precedence, seq(
            field('left', $._expression),
            field('operator', operator),
            field('right', $._expression),
          )),
        ),
      );
    },

    // Prefix operators (includes monadic lift ← for do-blocks)
    unary_expression: $ => prec(PREC.unary, seq(
      field('operator', choice('!', '¬', '-', '←', '<-')),
      field('operand', $._expression),
    )),

    // Explicit: `@ident` — suppresses implicit arguments
    explicit: $ => seq('@', $._atom),

    // Note: postfix `!` and `?` are handled by:
    // - subscript modifier: `arr[i]!`, `arr[i]?`
    // - notation system: `n !` (user-defined, parsed as application)

    // Lambda: `fun x => e` or `fun (x : T) => e` or `fun | pat => e | ...`
    // Body gets layout context so `let` bindings work properly
    fun: $ => prec.right(seq(
      choice('fun', 'λ'),
      choice(
        seq(
          field('binders', repeat1(choice($._pattern, $._bracketed_binder))),
          '=>',
          $._layout_start,
          field('body', $._expression),
          optional($._layout_end),
        ),
        repeat1($.match_arm),
      ),
    )),

    // Universal/existential quantifier: `∀ x, P x` or `∃ x, P x`
    quantifier: $ => prec.right(seq(
      field('quantifier', choice('forall', '∀', 'exists', '∃')),
      $._quantifier_tail,
    )),

    // Shared `binders, body` for forall and exists.
    _quantifier_tail: $ => seq(
      field('binders', $._quantifier_binders),
      ',',
      field('body', $._expression),
    ),

    // Have expression: `have h : T := proof; body`
    have: $ => prec.right(seq(
      'have',
      optional(field('name', $.identifier)),
      optional($._type_spec),
      $._binding_body,
    )),

    // Shared `:= value [; body]` tail for `let` and `have` — extracted
    // so the parser reuses states across both forms.
    _binding_body: $ => prec.right(seq(
      ':=',
      field('value', $._expression),
      optional(seq(
        choice(';', $._layout_semicolon),
        field('body', $._expression),
      )),
    )),

    // ============================================================
    // Tactic mode (entered via `by`)
    // Tactics are a separate syntactic category from expressions.
    // Expressions can contain `by` blocks, but never raw tactics.
    // ============================================================

    // `by` is the only entry point from expression world into tactic world.
    by: $ => prec.right(seq(
      'by',
      $._layout_start,
      $._tactic_seq,
      optional($._layout_end),
    )),

    // Tactics separated by `;`, `<;>` (broadcast), or newlines
    _tactic_seq: $ => prec.right(seq(
      $._tactic,
      repeat(seq(
        choice($._layout_semicolon, ';', '<;>', '<;'),
        $._tactic,
      )),
      optional(';'),
    )),

    // ── Tactic primitives ─────────────────────────────────────
    // Each rule here lives exclusively inside `by` blocks.
    // None of these appear in `_expression`.

    _tactic: $ => choice(
      $.tactic_apply,
      $.tactic_focus,
      $.tactic_case,
      $.tactic_rewrite,
      $.tactic_have,
      $.tactic_let,
      $.tactic_show,
      $.tactic_calc,
    ),

    // Most tactics: `intro n`, `simp [lemma]`, `apply foo`, `exact bar`, `omega`
    tactic_apply: $ => prec.right(PREC.app, seq(
      field('tactic', $.identifier),
      repeat(field('arg', choice(
        $._expression, $.tactic_config,
      ))),
    )),

    // Configuration list: `[lemma1, ←lemma2, *]`
    // The ← before lemmas is handled by unary_expression.
    tactic_config: $ => prec(1, seq(
      '[', commaSep($._expression), ']',
    )),

    // Focus: `· tactic1; tactic2`
    tactic_focus: $ => prec.right(seq(
      '·',
      $._layout_start,
      $._tactic_seq,
      optional($._layout_end),
    )),

    // Case split: `case name => ...` or `next => ...`
    tactic_case: $ => prec.right(seq(
      choice('case', 'next'),
      repeat($.identifier),
      '=>',
      $._layout_start,
      $._tactic_seq,
      optional($._layout_end),
    )),

    // `rw`/`rewrite` always take a config list, optionally with `at`
    tactic_rewrite: $ => prec.right(PREC.app, seq(
      choice('rw', 'rewrite'),
      choice(
        $.tactic_config,
        repeat1(field('arg', $._expression)),
      ),
      optional(seq('at', repeat1(choice($.identifier, '*')))),
    )),

    // `have h : T := proof` in tactic mode
    tactic_have: $ => prec.right(seq(
      choice('have', 'obtain', 'suffices'),
      optional(field('name', $._pattern)),
      optional($._type_spec),
      ':=',
      field('value', $._expression),
    )),

    // `let x := e` in tactic mode
    tactic_let: $ => prec(1, seq(
      'let',
      field('pattern', $._pattern),
      optional($._type_spec),
      ':=',
      field('value', $._expression),
    )),

    // `show T`
    tactic_show: $ => seq('show', $._expression),

    // `calc` block with steps
    tactic_calc: $ => prec.right(seq(
      'calc',
      $._layout_start,
      repeat1($.calc_step),
      optional($._layout_end),
    )),

    calc_step: $ => prec.right(seq(
      $._expression,
      ':=',
      $._expression,
    )),

    // Let binding: modeled after Lean's letDecl.
    // Lean tries letIdDecl first (identifier + optional binders), then letPatDecl.
    // `let x := e; body` — simple bind (identifier, 0 binders)
    // `let f (params) := e; body` — function (identifier + binders)
    // `let (a, b) := e; body` — pattern (tuple, hole — not constructor_pattern)
    let: $ => prec.right(choice(
      // Identifier form: always wins for bare identifiers.
      // Subsumes function form (with binders) and simple form (without).
      seq('let', field('name', $.identifier),
          optional(field('parameters', $.parameters)),
          optional($._type_spec), $._binding_body),
      // Pattern form: tuple destructuring and holes only.
      // Constructor patterns in `let` require qualified names, parsed differently.
      seq('let', field('pattern', choice($.tuple_pattern, $.hole)),
          optional($._type_spec), $._binding_body),
    )),

    // Lean's letIdBinder: binderIdent | bracketedBinder
    parameters: $ => repeat1(choice($.identifier, $._bracketed_binder)),

    // If expression: `if cond then t else e`
    // Also handles `if h : cond then t else e` (dependent if with hypothesis)
    if: $ => prec.right(seq(
      'if',
      optional(seq(field('hyp', $.identifier), ':')),
      field('condition', $._expression),
      $._then_else,
    )),

    // Shared `then expr [else expr]` tail for `if` and `if_let` — extracted
    // so the parser reuses states across both forms.
    _then_else: $ => prec.right(seq(
      'then',
      field('then', $._expression),
      optional(seq('else', field('else', $._expression))),
    )),

    // If-let pattern matching: `if let some x := e then ...`
    // Parsed as do-element or standalone, uses `let` keyword after `if`
    if_let: $ => prec.right(seq(
      'if',
      'let',
      field('pattern', $._pattern),
      choice(':=', '<-', '←'),
      field('value', $._expression),
      $._then_else,
    )),

    // Patterns for let, if-let, and match
    // Includes: identifiers, holes, tuples, constructor applications
    _pattern: $ => choice(
      $.identifier,
      $.hole,
      $.tuple_pattern,
      $.constructor_pattern,
    ),

    // Tuple pattern: `(a, b)` or `(a, b, c)`
    tuple_pattern: $ => seq(
      '(',
      $._pattern,
      ',',
      commaSep1($._pattern),
      ')',
    ),

    // List pattern: `[x]`, `[x, y]` — only in do_let to avoid
    // GLR conflict with instance_binder in fun binders.
    list_pattern: $ => seq('[', commaSep1($._pattern), ']'),

    // Constructor pattern: `some x`, `none`, `Foo.bar x y`
    // An identifier alone is just an identifier, not a constructor_pattern
    constructor_pattern: $ => prec.left(PREC.app, seq(
      field('constructor', $.identifier),
      repeat1(field('arg', $._pattern)),
    )),

    // Match expression (prec.left to consume as many arms as possible)
    match: $ => prec.left(seq(
      'match',
      field('scrutinees', commaSep1($._expression)),
      'with',
      repeat1($.match_arm),
    )),

    match_arm: $ => prec.right(seq(
      '|',
      field('patterns', commaSep1($._expression)),
      '=>',
      $._match_body_start,
      field('body', $._expression),
      optional($._layout_end),
    )),

    // Do notation with layout-sensitive parsing
    // Elements are separated by newlines at the same indentation level
    do: $ => prec.right(seq(
      'do',
      $._layout_start,
      $._do_seq,
      optional($._layout_end),
    )),

    // Sequence of do elements separated by layout semicolons or explicit semicolons
    _do_seq: $ => prec.right(seq(
      $._do_element,
      repeat(seq(
        choice($._layout_semicolon, ';'),
        $._do_element,
      )),
    )),

    _do_element: $ => choice(
      $.do_let,
      $.let_bind,
      $.let_mut,
      $.reassign,
      $.do_return,
      $.for_in,
      $.do_while,
      $.do_try,
      $.do_catch,
      $.do_if,
      $.do_if_let,
      $.do_match,
      $._expression,
    ),

    // Let in do-block: `let x := e` or `let [x] := e | fallback`
    do_let: $ => prec.right(2, seq(
      'let',
      field('pattern', choice($._pattern, $.list_pattern)),
      optional($._type_spec),
      ':=',
      field('value', $._expression),
      optional(seq('|', field('fallback', $._expression))),
    )),

    // Monadic bind: `let x ← e` or `let (a, b) ← e` or `let x : T ← e`
    let_bind: $ => seq(
      'let',
      field('name', $._pattern),
      optional($._type_spec),
      choice('<-', '←'),
      field('value', $._expression),
    ),

    // Mutable let: `let mut x := e` or `let mut x : Type := e`
    let_mut: $ => seq(
      'let',
      'mut',
      field('name', $.identifier),
      optional($._type_spec),
      choice('<-', '←', ':='),
      field('value', $._expression),
    ),

    // Reassignment: `x := e`
    // Low precedence so binary operators (+, *, etc.) shift into the value expression
    // rather than reducing the reassign early. The `:=` token already disambiguates
    // reassign from a bare expression in _do_element.
    reassign: $ => prec.right(1, seq(
      field('name', $.identifier),
      ':=',
      field('value', $._expression),
    )),

    // Using prec.left to prefer NOT consuming the next expression
    // (let the do-block parse it as a separate element)
    // Return should consume its value expression
    do_return: $ => prec.right(seq('return', optional(field('value', $._expression)))),

    // For loop: `for x in xs do body` or `for x in xs, y in ys do body`
    // Uses an explicit for_binding helper to help the parser generator
    // produce correct state transitions for multi-iterator loops.
    // Precedence > PREC.app so `do` is the for body, not an app argument.
    for_in: $ => prec.right(PREC.app + 1, seq(
      'for',
      $._for_binding,
      repeat(seq(',', $._for_binding)),
      field('body', $.do),
    )),

    // Precedence on the iterable > PREC.app so `do` reduces the expression
    // rather than being consumed as an application argument.
    _for_binding: $ => seq(
      field('var', choice($._pattern, $.structure_instance)),
      'in',
      field('iterable', prec(PREC.app + 1, $._expression)),
    ),

    // If in do-block: branches are do-sequences (can contain reassignment etc.)
    do_if: $ => prec.right(1, seq(
      'if',
      optional(seq(field('hyp', $.identifier), ':')),
      field('condition', $._expression),
      $._do_then_else,
    )),

    // Shared `then do_seq [else do_seq]` for do_if and do_if_let.
    _do_then_else: $ => prec.right(seq(
      'then',
      $._layout_start,
      field('then', $._do_seq),
      optional($._layout_end),
      optional(seq(
        'else',
        $._layout_start,
        field('else', $._do_seq),
        optional($._layout_end),
      )),
    )),

    // If-let in do-block: `if let some x := e then ...`
    do_if_let: $ => prec.right(1, seq(
      'if',
      'let',
      field('pattern', $._pattern),
      choice(':=', '<-', '←'),
      field('value', $._expression),
      $._do_then_else,
    )),

    // Match in do-block: arms have do-sequences as bodies.
    // Arms are delimited by `|` — the scanner suppresses LAYOUT_SEMICOLON
    // before `|` so that _do_seq doesn't consume it.
    do_match: $ => prec.left(1, seq(
      'match',
      field('scrutinees', commaSep1($._expression)),
      'with',
      repeat1($.do_match_arm),
    )),

    // Match arm body uses layout to support multi-line do-sequences.
    // The `|` at the start of the next arm triggers layout_end for the current arm body.
    do_match_arm: $ => prec.right(seq(
      '|',
      field('patterns', commaSep1($._expression)),
      '=>',
      $._layout_start,
      field('body', $._do_seq),
      optional($._layout_end),
    )),

    // While loop in do-block: `while cond do body`
    do_while: $ => prec.right(1, seq(
      'while',
      field('condition', $._expression),
      field('body', $.do),
    )),

    // Try in do-blocks: `try body`
    // Catch is a sibling _do_element because LAYOUT_SEMICOLON fires
    // between the try body and `catch` at the same indent level.
    do_try: $ => prec.right(seq(
      'try',
      $._layout_start,
      field('body', $._do_seq),
      optional($._layout_end),
    )),

    // Catch handler: `catch e => expr`
    do_catch: $ => prec.right(seq(
      'catch',
      optional(field('var', $.identifier)),
      '=>',
      field('handler', $._expression),
    )),

    // ============================================================
    // Delimited Expressions
    // ============================================================

    parenthesized: $ => seq(
      '(',
      optional(seq(
        $._expression,
        optional(seq(':', field('type', $._expression))),
      )),
      ')',
    ),

    // Named argument: `(name := value)`
    named_argument: $ => seq(
      '(',
      field('name', $.identifier),
      ':=',
      field('value', $._expression),
      ')',
    ),

    tuple: $ => seq(
      '(',
      $._expression,
      ',',
      commaSep1($._expression),
      ')',
    ),

    anonymous_constructor: $ => seq('⟨', commaSep($._expression), '⟩'),

    // Subtype: `{x // P}` or `{x : T // P}`
    subtype: $ => seq(
      '{',
      field('var', $.identifier),
      optional($._type_spec),
      '//',
      field('property', $._expression),
      '}',
    ),

    structure_instance: $ => seq(
      '{',
      optional($._structure_body),
      '}',
    ),

    // Extracted to reduce combinatorial explosion from 3 optionals
    // (extends, fields, type) inside the braces.
    _structure_body: $ => choice(
      seq(field('extends', $._expression), 'with',
        optional(seq(
          choice($.field_assignment, $.ellipsis),
          repeat(seq(choice(',', /\n/), choice($.field_assignment, $.ellipsis))),
        )),
        optional($._type_spec)),
      seq(
        choice($.field_assignment, $.ellipsis),
        repeat(seq(choice(',', /\n/), choice($.field_assignment, $.ellipsis))),
        optional($._type_spec)),
      $._type_spec,
    ),

    field_assignment: $ => choice(
      // Full form: `name := value`
      seq(
        field('name', $.identifier),
        ':=',
        field('value', $._expression),
      ),
      // Short form: `name` (when variable name matches field name)
      field('name', $.identifier),
    ),

    array: $ => seq('#[', commaSep($._expression), ']'),

    list: $ => seq('[', commaSep($._expression), ']'),

    // Range syntax: `[:n]`, `[start:end]`, `[start:end:step]`
    range: $ => seq('[', $._range_spec, ']'),

    // Extracted range internals to separate the 3 optional expression
    // slots from the surrounding brackets.
    _range_spec: $ => seq(
      optional(field('start', $._expression)),
      ':',
      optional(field('end', $._expression)),
      optional(seq(':', field('step', $._expression))),
    ),

    // ============================================================
    // Atoms
    // ============================================================

    // Identifier with optional dot-separated parts: `Foo.Bar.baz`
    // Simple identifier without dots - projection handles qualified access
    identifier: _ => /[_a-zA-Zα-ωΑ-Ωℕℤℚℝℂ∇][_a-zA-Z0-9'α-ωΑ-Ωℕℤℚℝℂ∇?!]*/,

    // Escaped identifier: `«name with spaces»`
    escaped_identifier: _ => /«[^»]*»/,

    float: _ => token(prec(1, seq(/\d+/, '.', optional(/\d+/)))),

    number: _ => choice(
      /\d+/,                    // decimal
      /0x[0-9a-fA-F]+/,         // hex
      /0b[01]+/,                // binary
      /0o[0-7]+/,               // octal
    ),

    string: $ => seq(
      '"',
      repeat(choice(
        $._string_content,
        $.escape_sequence,
        $.interpolation,
      )),
      '"',
    ),

    _string_content: _ => token.immediate(prec(1, /[^"\\{]+/)),

    escape_sequence: _ => token.immediate(seq(
      '\\',
      choice(
        /[\\'"nrt0]/,
        /x[0-9a-fA-F]{2}/,
        /u[0-9a-fA-F]{4}/,
        /u\{[0-9a-fA-F]+\}/,
      ),
    )),

    interpolation: $ => seq('{', $._expression, '}'),

    char: _ => seq("'", choice(/[^'\\]/, /\\./), "'"),

    // Hole/placeholder: `_`
    hole: _ => '_',

    // Cdot: `·` (sugared anonymous function placeholder)
    cdot: _ => '·',

    // Synthetic hole: `?foo` or `?_`
    synthetic_hole: _ => /\?[_a-zA-Z]\w*/,

    // Quoted name: `` `name `` or ``` ``name ```
    quoted_name: $ => seq('`', $.identifier),
    double_quoted_name: $ => seq('``', $.identifier),

    // Ellipsis argument: `..`
    ellipsis: _ => '..',

    sorry: _ => 'sorry',

    _boolean: $ => choice($.true, $.false),
    true: _ => choice('true', 'True'),
    false: _ => choice('false', 'False'),

    // ============================================================
    // Comments
    // ============================================================

    comment: _ => token(choice(
      seq('--', /.*/),
      seq('/-', /[^-]*(-+[^-/][^-]*)*-*/, '-/'),
    )),
  },
});
