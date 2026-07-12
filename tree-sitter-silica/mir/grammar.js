// Silica MIR grammar.
//
// MIR is the statement-oriented CFG-based intermediate representation.
// Shared lexical, marker, type, and struct/enum decl rules live in
// `../common/grammar.js` and are spread into `rules` below. Rules
// defined here are MIR-specific: places, operands, rvalues, statements,
// terminators, basic blocks, and function bodies.

const common = require('../common/grammar.js');

module.exports = grammar({
  name: 'silica_mir',

  extras: $ => [
    /\s+/,
    $.comment,
  ],

  word: $ => $.identifier,

  rules: {
    program: $ => repeat($.declaration),

    declaration: $ => choice(
      $.struct_decl,
      $.enum_decl,
      $.function_decl,
    ),

    ...common.rules,

    // MIR struct/enum decls: separators between fields are either
    // whitespace or `,`. Existing test programs use whitespace-only;
    // commas are also accepted so hand-written MIR can use whichever
    // reads best.
    struct_decl: $ => seq(
      'struct',
      optional($.markers),
      field('name', $.identifier),
      '{',
      repeat(seq($.struct_field, optional(','))),
      '}',
    ),
    enum_decl: $ => seq(
      'enum',
      optional($.markers),
      field('name', $.identifier),
      '{',
      repeat(seq($.enum_variant, optional(','))),
      '}',
    ),

    param_decl: $ => seq(
      field('name', $.identifier),
      ':',
      field('type', $.type),
    ),

    local_decl: $ => seq(
      field('name', $.identifier),
      ':',
      field('type', $.type),
      ';',
    ),

    function_decl: $ => choice(
      seq(
        'extern', 'fn',
        field('name', $.identifier),
        '(', common.commaSep($.param_decl), ')',
        ';',
      ),
      seq(
        'fn',
        field('name', $.identifier),
        '(', common.commaSep($.param_decl), ')',
        '{', repeat($.local_decl), repeat($.basic_block), '}',
      ),
    ),

    basic_block: $ => seq(
      field('label', $.identifier),
      ':',
      repeat(seq($.statement, ';')),
      $.terminator,
    ),

    statement: $ => choice(
      $.assignment,
      $.call,
      $.drop_stmt,
      $.unborrow_stmt,
    ),

    drop_stmt: $ => seq(
      'drop',
      field('place', $.place),
    ),

    unborrow_stmt: $ => seq(
      'unborrow',
      field('place', $.place),
    ),

    assignment: $ => seq(
      field('lhs', $.place),
      '=',
      field('rhs', $.rvalue),
    ),

    call: $ => seq(
      'call',
      field('function', $.operand),
      '(',
      common.commaSep($.operand),
      ')',
    ),

    terminator: $ => choice(
      $.goto,
      $.return,
      $.branch,
      $.switchEnum,
      $.abort,
      $.unreachable,
    ),

    goto: $ => seq(
      'goto',
      field('label', $.identifier),
    ),

    return: $ => 'return',

    branch: $ => seq(
      'branch',
      '(',
      field('condition', $.operand),
      ')',
      '[',
      'true',
      ':',
      field('true_label', $.identifier),
      ',',
      'false',
      ':',
      field('false_label', $.identifier),
      ']',
    ),

    switchEnum: $ => seq(
      'switchEnum',
      '(',
      field('place', $.place),
      ')',
      '[',
      common.commaSep($.switch_case),
      ']',
    ),

    switch_case: $ => seq(
      field('variant', $.identifier),
      ':',
      field('label', $.identifier),
    ),

    abort: $ => 'abort',

    unreachable: $ => 'unreachable',

    place: $ => choice(
      $.identifier, // var
      prec.left(2, seq($.place, '.', field('field', $.identifier))),
      prec.left(2, seq($.place, 'as', field('variant', $.identifier))),
      // Array indexing: dynamic operand. Const-integer operands are
      // trackable per-slot; non-const operands widen to whole-array.
      prec.left(2, seq($.place, '[', field('index', $.operand), ']')),
      prec.left(3, seq($.place, '.', '*')),
    ),

    operand: $ => choice(
      seq('copy', $.place),
      seq('move', $.place),
      $.const,
    ),

    const: $ => choice(
      $.float_lit,   // ordered before int_lit so `3.14` isn't lexed as int
      $.int_lit,
      $.byte_str_lit,
      $.byte_char_lit,
      'true',
      'false',
      'unit',
      $.identifier, // fnName
    ),

    rvalue: $ => choice(
      $.operand,
      seq('&', $.place),
      seq('&mut', $.place),
      seq('&out', $.place),
      seq('&drop', $.place),
      seq('&uninit', $.place),
      // Raw pointer (unsafe): does not create a loan, no aliasing
      // guarantees, no init-state obligation. Deref is unchecked.
      seq('&raw', $.place),
      seq(field('enum_name', $.identifier), '::', field('variant_name', $.identifier), '(', $.operand, ')'),
      // Aggregate array literal: [e0, e1, ..., eN-1]. All operands
      // must share the array's element type.
      seq('[', common.commaSep($.operand), ']'),
    ),
  },
});
