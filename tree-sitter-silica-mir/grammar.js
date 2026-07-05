module.exports = grammar({
  name: 'silica_mir',

  extras: $ => [
    /\s+/,
    $.comment
  ],

  word: $ => $.identifier,

  rules: {
    program: $ => repeat($.declaration),

    declaration: $ => choice(
      $.struct_decl,
      $.enum_decl,
      $.function_decl
    ),

    comment: $ => /#.*/,

    identifier: $ => /[a-zA-Z_][a-zA-Z0-9_]*/,
    number: $ => /[0-9]+/,

    struct_decl: $ => seq(
      'struct',
      optional($.markers),
      field('name', $.identifier),
      '{',
      repeat($.struct_field),
      '}'
    ),

    struct_field: $ => seq(
      field('name', $.identifier),
      ':',
      field('type', $.type)
    ),

    enum_decl: $ => seq(
      'enum',
      optional($.markers),
      field('name', $.identifier),
      '{',
      repeat($.enum_variant),
      '}'
    ),

    enum_variant: $ => seq(
      field('name', $.identifier),
      ':',
      field('type', $.type)
    ),

    markers: $ => choice(
      'Copy',
      'Drop',
      seq('Copy', 'Drop'),
      seq('Drop', 'Copy')
    ),



    param_decl: $ => seq(
      field('name', $.identifier),
      ':',
      field('type', $.type)
    ),

    local_decl: $ => seq(
      field('name', $.identifier),
      ':',
      field('type', $.type),
      ';'
    ),

    function_decl: $ => choice(
      seq(
        'extern', 'fn',
        field('name', $.identifier),
        '(', commaSep($.param_decl), ')',
        ';'
      ),
      seq(
        'fn',
        field('name', $.identifier),
        '(', commaSep($.param_decl), ')',
        '{', repeat($.local_decl), repeat($.basic_block), '}'
      )
    ),

    basic_block: $ => seq(
      field('label', $.identifier),
      ':',
      repeat(seq($.statement, ';')),
      $.terminator
    ),

    statement: $ => choice(
      $.assignment,
      $.call,
      $.drop_stmt
    ),

    drop_stmt: $ => seq(
      'drop',
      field('place', $.place)
    ),

    assignment: $ => seq(
      field('lhs', $.place),
      '=',
      field('rhs', $.rvalue)
    ),

    call: $ => seq(
      'call',
      field('function', $.operand),
      '(',
      commaSep($.operand),
      ')'
    ),

    terminator: $ => choice(
      $.goto,
      $.return,
      $.branch,
      $.switchEnum,
      $.abort,
      $.unreachable
    ),

    goto: $ => seq(
      'goto',
      field('label', $.identifier)
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
      ']'
    ),

    switchEnum: $ => seq(
      'switchEnum',
      '(',
      field('place', $.place),
      ')',
      '[',
      commaSep($.switch_case),
      ']'
    ),

    switch_case: $ => seq(
      field('variant', $.identifier),
      ':',
      field('label', $.identifier)
    ),

    abort: $ => 'abort',

    unreachable: $ => 'unreachable',

    place: $ => choice(
      $.identifier, // var
      prec.left(2, seq($.place, '.', field('field', $.identifier))),
      prec.left(2, seq($.place, 'as', field('variant', $.identifier))),
      prec.left(1, seq('*', $.place))
    ),

    operand: $ => choice(
      seq('copy', $.place),
      seq('move', $.place),
      $.const
    ),

    const: $ => choice(
      $.number,
      'true',
      'false',
      'unit',
      $.identifier // fnName
    ),

    rvalue: $ => choice(
      $.operand,
      seq('&', $.place),
      seq('&mut', $.place),
      seq('&out', $.place),
      seq('&drop', $.place),
      seq('&uninit', $.place),
      seq(field('enum_name', $.identifier), '::', field('variant_name', $.identifier), '(', $.operand, ')')
    ),

    type: $ => choice(
      'number',
      'boolean',
      'unit',
      prec(2, seq('&', $.type)),
      prec(2, seq('&mut', $.type)),
      prec(2, seq('&out', $.type)),
      prec(2, seq('&drop', $.type)),
      prec(2, seq('&uninit', $.type)),
      seq('fn', '(', commaSep($.type), ')'),
      $.identifier // struct / enum name
    )
  }
});

function commaSep(rule) {
  return optional(seq(rule, repeat(seq(',', rule))));
}
