// Silica HLL grammar.
//
// The HLL is expression-oriented with implicit control flow —
// `if`, `match`, `loop`, blocks, `let`. Statements terminate with
// `;`; the last expression in a block is the block's value.
//
// Shared with MIR (via `../common/grammar.js`): lexical tokens,
// marker keywords, `type`, `struct_decl`, `enum_decl`. Everything
// else in `rules` below is HLL-specific.
//
// The HLL currently has no arithmetic/comparison operators —
// those go through intrinsic function calls when the HLL is
// lowered to MIR. When surface operators land, they slot into
// the precedence ladder between `prefix` and `postfix`.

const common = require('../common/grammar.js');

module.exports = grammar({
  name: 'silica',

  extras: $ => [
    /\s+/,
    $.comment,
  ],

  word: $ => $.identifier,

  // The `Ident {` prefix is ambiguous between a struct constructor
  // (`Point { x: 1 }`) and a plain identifier followed by a block
  // (`if cond { ... }`). Tree-sitter explores both interpretations;
  // `struct_constr`'s body only matches `field_init` (name `:` expr),
  // so ambiguous cases where the block contents don't shape like
  // fields resolve to the identifier-then-block interpretation.
  conflicts: $ => [
    [$._expr_primary, $.struct_constr],
  ],

  rules: {
    program: $ => repeat($.declaration),

    declaration: $ => choice(
      $.struct_decl,
      $.enum_decl,
      $.fn_decl,
    ),

    ...common.rules,

    // HLL type grammar: shared alternatives plus `fn(T,...)` with
    // an optional `-> R` return arrow. Return type defaults to
    // `unit` when the arrow is omitted.
    type: $ => choice(
      ...common.typeChoices($),
      seq(
        'fn',
        '(', common.commaSep($.type), ')',
        optional(seq('->', field('return_type', $.type))),
      ),
    ),

    // HLL struct/enum decls: mandatory comma between fields.
    // `commaSep` already tolerates a trailing comma.
    struct_decl: $ => seq(
      'struct',
      field('name', $.identifier),
      optional($.markers),
      '{',
      common.commaSep($.struct_field),
      '}',
    ),
    enum_decl: $ => seq(
      'enum',
      field('name', $.identifier),
      optional($.markers),
      '{',
      common.commaSep($.enum_variant),
      '}',
    ),

    // `fn name(params) [-> type] block`. Return type defaults to
    // `unit` when the arrow is omitted. Body is a block expression.
    fn_decl: $ => seq(
      'fn',
      field('name', $.identifier),
      '(', common.commaSep($.param_decl), ')',
      optional(seq('->', field('return_type', $.type))),
      field('body', $.block_expr),
    ),

    param_decl: $ => seq(
      field('name', $.identifier),
      ':',
      field('type', $.type),
    ),

    // Statement: either a `let` binding or an expression followed
    // by `;`. The trailing expression of a block (without `;`) is
    // parsed by `block_expr`, not here.
    stmt: $ => choice(
      $.let_stmt,
      $.defer_stmt,
      seq($.expr, ';'),
    ),

    defer_stmt: $ => seq(
      'defer',
      field('body', $.expr),
      ';',
    ),

    let_stmt: $ => seq(
      'let',
      optional('mut'),
      field('name', $.identifier),
      optional(seq(':', field('type', $.type))),
      '=',
      field('init', $.expr),
      ';',
    ),

    // Expression grammar — a single `expr` rule with precedence
    // tiers via `prec`. Lower `prec` number binds looser.
    // Ladder (loose → tight): assignment → prefix → postfix → primary.
    //
    // Each operator gets its own NAMED rule (no leading underscore)
    // so the CST has nested structure — `n.*.value` becomes
    // `field_access(deref(n), value)` rather than a flat list. This
    // is what the CST-to-AST walker in parser.rs expects. Hidden
    // wrapper rules (`_expr_*`) only choose which alternative
    // applies at each precedence tier.
    expr: $ => $._expr_assignment,

    _expr_assignment: $ => choice(
      $._expr_prefix,
      $.assign_expr,
    ),

    assign_expr: $ => prec.right(1, seq(
      field('lhs', $._expr_prefix),
      '=',
      field('rhs', $._expr_assignment),
    )),

    _expr_prefix: $ => choice(
      $._expr_postfix,
      $.borrow_expr,
      $.raw_borrow_expr,
      $.binary_expr,
    ),

    borrow_expr: $ => prec(10, seq(
      field('kind', choice('&', '&mut', '&out', '&deinit', '&uninit')),
      field('target', $._expr_prefix),
    )),

    raw_borrow_expr: $ => prec(10, seq(
      '&raw',
      field('target', $._expr_prefix),
    )),

    binary_expr: $ => choice(
      prec.left(13, seq(field('lhs', $.expr), field('op', choice('*', '/', '%')), field('rhs', $.expr))),
      prec.left(12, seq(field('lhs', $.expr), field('op', choice('+', '-')), field('rhs', $.expr))),
      prec.left(10, seq(field('lhs', $.expr), field('op', choice('<', '>', '<=', '>=')), field('rhs', $.expr))),
      prec.left(9, seq(field('lhs', $.expr), field('op', choice('==', '!=')), field('rhs', $.expr))),
    ),

    // Postfix chains bind left-to-right and tightly. Each gets its
    // own named rule so the CST is nested (see comment above).
    _expr_postfix: $ => choice(
      $._expr_primary,
      $.field_access,
      $.deref_expr,
      $.downcast_expr,
      $.call_expr,
      $.index_expr,
      $.match_expr,
    ),

    field_access: $ => prec.left(20, seq(
      field('target', $._expr_postfix),
      '.',
      field('field', $.identifier),
    )),

    deref_expr: $ => prec.left(20, seq(
      field('target', $._expr_postfix),
      '.',
      '*',
    )),

    downcast_expr: $ => prec.left(20, seq(
      field('target', $._expr_postfix),
      'as',
      field('variant', $.identifier),
    )),

    call_expr: $ => prec.left(20, seq(
      field('function', $._expr_postfix),
      '(',
      common.commaSep($.expr),
      ')',
    )),

    index_expr: $ => prec.left(20, seq(
      field('target', $._expr_postfix),
      '[',
      field('index', $.expr),
      ']',
    )),

    // Match is a postfix operator on the scrutinee, mirroring the
    // hand-rolled HLL: `expr match { arms }`.
    match_expr: $ => prec.left(20, seq(
      field('scrutinee', $._expr_postfix),
      'match',
      '{',
      common.commaSep($.match_arm),
      '}',
    )),

    _expr_primary: $ => choice(
      $.int_lit,
      $.float_lit,
      $.bool_lit,
      $.unit_lit,
      $.paren_expr,
      $.block_expr,
      $.if_expr,
      $.loop_expr,
      $.break_expr,
      $.continue_expr,
      $.return_expr,
      $.struct_constr,
      $.enum_constr,
      $.array_lit,
      // Plain identifier reference (variable or function name).
      $.identifier,
    ),

    bool_lit: $ => choice('true', 'false'),
    unit_lit: $ => 'unit',

    // Parenthesized expression, also serves as unit `()`.
    paren_expr: $ => choice(
      seq('(', ')'),
      seq('(', $.expr, ')'),
    ),

    // Block expression: `{ stmt* trailing_expr? }`. The trailing
    // expression (an `expr` not followed by `;`) is the block's
    // value; without a trailing expression the block evaluates to
    // unit.
    block_expr: $ => seq(
      '{',
      repeat($.stmt),
      optional(field('tail', $.expr)),
      '}',
    ),

    if_expr: $ => prec.right(seq(
      'if',
      field('cond', $.expr),
      field('then', $.block_expr),
      optional(seq('else', field('else', $.block_expr))),
    )),

    loop_expr: $ => seq('loop', field('body', $.block_expr)),

    break_expr: $ => prec.right(seq('break', optional($.expr))),
    continue_expr: $ => 'continue',
    return_expr: $ => prec.right(seq('return', optional($.expr))),

    // Struct constructor `Name { field: value, ... }`. Requires
    // at least the `field:` shape after `{` (or empty braces) so
    // the parser doesn't confuse `if cond { block }` for a struct
    // literal — matches the hand-rolled parser's heuristic.
    // Higher static precedence than the naked identifier alternative
    // in `_expr_primary` so `Name {` prefers this rule.
    struct_constr: $ => prec.dynamic(1, seq(
      field('name', $.identifier),
      '{',
      common.commaSep($.field_init),
      '}',
    )),

    field_init: $ => seq(
      field('name', $.identifier),
      ':',
      field('value', $.expr),
    ),

    enum_constr: $ => seq(
      field('name', $.identifier),
      '::',
      field('variant', $.identifier),
      '(',
      field('payload', $.expr),
      ')',
    ),

    array_lit: $ => seq('[', common.commaSep($.expr), ']'),

    // Match arm. Pattern is a variant name, optionally binding the
    // payload via `Variant(bound_var)`. Unit-variant arms omit the
    // parenthesized binder.
    match_arm: $ => seq(
      field('pattern', $.pattern),
      '=>',
      field('body', $.expr),
    ),

    pattern: $ => seq(
      field('variant', $.identifier),
      optional(seq(
        '(',
        field('bound', $.identifier),
        ')',
      )),
    ),
  },
});
