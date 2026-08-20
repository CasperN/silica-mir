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
      $.trait_decl,
      $.impl_decl,
    ),

    ...common.rules,

    type: $ => choice(
      'unit',
      ...common.typeChoices($),
      // MIR specific fn type: `fn [abi] (T, ..., [$return:] T)`.
      seq(
        'fn',
        optional(field('abi', $.string_lit)),
        '(',
        common.commaSep(choice(
          $.type,
          seq(field('return_marker', '$return'), ':', field('return_ty', $.type)),
        )),
        ')',
      ),
    ),

    // MIR struct/enum decls: separators between fields are either
    // whitespace or `,`. Existing test programs use whitespace-only;
    // commas are also accepted so hand-written MIR can use whichever
    // reads best.
    //
    struct_decl: $ => seq(
      'struct',
      field('name', $.identifier),
      optional($.type_params),
      optional($.markers),
      '{',
      repeat(seq($.struct_field, optional(','))),
      '}',
    ),
    enum_decl: $ => seq(
      'enum',
      field('name', $.identifier),
      optional($.type_params),
      optional($.markers),
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

    function_decl: $ => seq(
      optional(field('extern', 'extern')),
      optional(field('abi', $.string_lit)),
      'fn',
      field('name', $.identifier),
      optional($.type_params),
      '(', common.commaSep($.param_decl), ')',
      choice(
        ';',
        seq('{', repeat($.local_decl), repeat($.basic_block), '}'),
      ),
    ),

    // Trait declaration: name + optional generics + a body of method
    // signatures. Signatures reuse `function_decl` in its body-omitted
    // form (matches `extern fn` shape) — the type checker rejects
    // methods with bodies at this position.
    //
    // `Self` is a reserved identifier bound implicitly in the trait's
    // scope; methods reference it as `Self` and impls substitute it
    // with the target type.
    trait_decl: $ => seq(
      'trait',
      field('name', $.identifier),
      optional($.type_params),
      optional($.trait_bounds),
      '{',
      repeat($.function_decl),
      '}',
    ),

    // Trait impl: `impl<T> Trait<TypeArgs> for TargetType { methods }`.
    // Inherent impl: `impl<T> TargetType { methods }`.
    // Header generics (`<T>`) are the impl's own; they bind for the
    // optional trait ref, target type, and every method sig/body.
    // The target type fills the methods' `Self` slot. Trait impl methods
    // are additionally checked against the trait declaration.
    impl_decl: $ => seq(
      'impl',
      optional($.type_params),
      choice(
        seq(
          field('trait_name', $.identifier),
          optional($.type_args),
          'for',
          field('target', $.type),
        ),
        field('target', $.type),
      ),
      '{',
      repeat($.function_decl),
      '}',
    ),

    basic_block: $ => seq(
      field('label', $.identifier),
      ':',
      repeat(seq($.statement, ';')),
      $.terminator,
      optional(';'),
    ),

    statement: $ => choice(
      $.assignment,
      $.call,
      $.drop_stmt,
      $.unborrow_stmt,
      $.require_uninit_stmt,
    ),

    drop_stmt: $ => seq(
      'drop',
      field('place', $.place),
    ),

    unborrow_stmt: $ => seq(
      'unborrow',
      field('place', $.place),
    ),

    require_uninit_stmt: $ => seq(
      'require_uninit',
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
      seq('take', $.place),
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
      $.fn_name,
    ),

    // Function name const. Two shapes:
    //
    //   foo                        — free fn, optionally with type args:
    //   foo<i32, bool>               `ConstVal::FnName(name, args)`.
    //
    //   <SelfTy as Trait<Args>>::method<MethodArgs>
    //                              — trait-method callee (UFCS-style):
    //                                `ConstVal::TraitFn { trait_path,
    //                                self_ty, method }`. The `as`
    //                                keyword disambiguates from a plain
    //                                `<` starting type_args.
    //
    // Codegen internal-errors on non-empty type args until
    // monomorphization lands.
    fn_name: $ => choice(
      seq($.identifier, optional($.type_args)),
      seq(
        '<',
        field('self_ty', $.type),
        '>',
        '::',
        field('method_name', $.identifier),
        optional(field('method_args', $.type_args)),
      ),
      seq(
        '<',
        field('self_ty', $.type),
        'as',
        field('trait_name', $.identifier),
        optional(field('trait_args', $.type_args)),
        '>',
        '::',
        field('method_name', $.identifier),
        optional(field('method_args', $.type_args)),
      ),
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
      // Generic enum construction may carry type args:
      //   Option<i64>::Some(42). No turbofish needed — Silica has no
      //   `<` operator so `Name<Args>::Variant` is unambiguous.
      seq(
        field('enum_name', $.identifier),
        optional($.type_args),
        '::',
        field('variant_name', $.identifier),
        '(', $.operand, ')',
      ),
      // Aggregate array literal: [e0, e1, ..., eN-1]. All operands
      // must share the array's element type.
      seq('[', common.commaSep($.operand), ']'),
      $.pointer_cast,
    ),

    pointer_cast: $ => seq(
      'ptr_cast',
      '(',
      field('value', $.operand),
      ',',
      field('type', $.type),
      ')'
    ),
  },
});
