// Shared tree-sitter grammar rules for Silica HLL and MIR.
//
// This module is not itself a tree-sitter grammar — it exports a
// plain object mapping rule names to builder functions. Each Silica
// language grammar (`hll/grammar.js`, `mir/grammar.js`) spreads these
// rules into its own rule map with `...common` so both languages
// share one canonical definition of lexical tokens, types, marker
// keywords, and struct/enum declarations. Grammar-level drift between
// the two languages is impossible for anything defined here.
//
// The `$`, `choice`, `seq`, `field`, `optional`, `repeat`, `prec`, and
// `commaSep` helpers used below come from the tree-sitter grammar DSL,
// which is in scope wherever a grammar.js is evaluated by
// `tree-sitter generate`.

// Comma-separated list of `rule`, with an optional trailing comma
// after the last element. Used for struct/enum decls, function args,
// tuples, arrays, etc. — anywhere a Rust-style trailing comma should
// be tolerated.
function commaSep(rule) {
  return optional(seq(rule, repeat(seq(',', rule)), optional(',')));
}

// Shared alternatives for the `type` grammar rule. Returned as an
// array so each language grammar can spread these into its own
// `type: choice(...)` alongside a language-specific `fn(...)` variant
// — HLL has `fn(T,...) [-> R]`, MIR has `fn(T,...)` with no arrow.
// `$` is the calling grammar's `$` so `$.type` recurses correctly.
//
// The identifier form accepts optional `type_args` (`Foo<T, U>`).
// Both languages see the same syntactic form; parsers resolve a
// bare identifier to either a decl reference or an in-scope type
// parameter using their own scope tracking.
function typeChoices($) {
  return [
    'i8', 'i16', 'i32', 'i64',
    'u8', 'u16', 'u32', 'u64',
    'f32', 'f64',
    'bool',
    'unit',
    'never',
    prec(2, seq('&', optional($.lifetime), $.type)),
    prec(2, seq('&mut', optional($.lifetime), $.type)),
    prec(2, seq('&out', optional($.lifetime), $.type)),
    prec(2, seq('&drop', optional($.lifetime), $.type)),
    prec(2, seq('&uninit', optional($.lifetime), $.type)),
    prec(2, seq('*', $.type)),
    seq('[', field('element', $.type), ';', field('length', $.int_lit), ']'),
    seq($.identifier, optional($.type_args)), // struct/enum name or type var; optional args
  ];
}

module.exports = {
  commaSep,
  typeChoices,

  rules: {
    // Line comment. Same syntax in both languages: `# ...` to end of line.
    comment: $ => /#.*/,

    // Identifiers may optionally start with `$` — a reserved namespace
    // for MIR-only names (intrinsics, compiler-generated symbols) that
    // the higher-level language forbids in user code. Guarantees no
    // HLL name can shadow an intrinsic.
    identifier: $ => /\$?[a-zA-Z_][a-zA-Z0-9_]*/,

    lifetime: $ => /'[a-zA-Z_][a-zA-Z0-9_]*/,

    // Integer literals: decimal / hex (0x…) / binary (0b…). Underscore
    // separators allowed anywhere in the digits. Optional type suffix
    // pins the type; unsuffixed defaults to i64 at parse time.
    int_lit: $ =>
      /(0x[0-9a-fA-F_]+|0b[01_]+|[0-9][0-9_]*)(i8|i16|i32|i64|u8|u16|u32|u64)?/,

    // Float literals: decimal only (hex floats not supported yet).
    // Underscore separators allowed. Optional f32/f64 suffix;
    // unsuffixed defaults to f64.
    float_lit: $ => /[0-9][0-9_]*\.[0-9][0-9_]*(f32|f64)?/,

    // Byte string literal: `b"..."`. Supports common escape sequences
    // (\n, \t, \r, \0, \\, \", and \xNN hex bytes). Value type is
    // `[u8; N]` where N is the decoded byte count. No UTF-8 or
    // unicode escapes — use \xNN for non-ASCII bytes.
    byte_str_lit: $ => /b"([^"\\]|\\.)*"/,

    // Byte character literal: `b'X'`. One ASCII byte or one escape
    // sequence (including `\xNN`). Value type is `u8`.
    byte_char_lit: $ => /b'([^'\\]|\\x[0-9a-fA-F]{2}|\\.)'/,

    string_lit: $ => /"[^"]*"/,

    // Substructural marker keywords on a struct or enum declaration.
    // Any subset of {Copy, Drop, Move} in any order, no duplicates
    // (duplicate check is enforced by the parser, not the grammar).
    // Syntax: `: Copy + Drop`. The leading `:` is required whenever
    // markers are present; absent markers means the type is linear.
    marker: $ => choice('Copy', 'Drop', 'Move'),
    markers: $ => seq(
      ':',
      $.marker,
      repeat(seq('+', $.marker)),
    ),

    // Generic parameter clause on a decl: `<'a, T, U: Move + Copy>`.
    // Accepts a mix of lifetime and type parameters in any order; the
    // parser buckets them into `lifetime_params` and `type_params`.
    // Rust convention is lifetimes-first; not grammar-enforced today.
    type_param: $ => seq(
      field('name', $.identifier),
      optional($.markers),
    ),
    _generic_param: $ => choice($.lifetime, $.type_param),
    type_params: $ => seq(
      '<',
      $._generic_param,
      repeat(seq(',', $._generic_param)),
      optional(','),
      '>',
    ),

    // Type arguments at a use site: `Foo<'a, i32, T>` or `call fn<T>(...)`.
    // Parsers resolve these against the current decl's parameter scope;
    // use-site bound satisfaction is checked in the type-check pass.
    _type_arg: $ => choice($.lifetime, $.type),
    type_args: $ => seq(
      '<',
      $._type_arg,
      repeat(seq(',', $._type_arg)),
      optional(','),
      '>',
    ),

    // Struct/enum field and variant have identical inner shape
    // (`name : type`) in both languages. Each language defines its
    // own `struct_decl` / `enum_decl` wrapper because field
    // separators differ: MIR is whitespace-only, HLL uses commas.
    struct_field: $ => seq(
      field('name', $.identifier),
      ':',
      field('type', $.type),
    ),
    enum_variant: $ => seq(
      field('name', $.identifier),
      ':',
      field('type', $.type),
    ),

    // NOTE: `type` is defined per-language, not here. Each language
    // grammar composes the shared alternatives (`typeChoices($)`)
    // with its own `fn(...)` variant — HLL includes the optional
    // return arrow, MIR does not.
  },
};
