# AGENTS.md

Agent-facing conventions for the Silica compiler.

Current compiler behavior is defined by code and tests. This file records
stable semantics, engineering invariants, and workflow conventions that are
expensive to rediscover. It deliberately does not duplicate fast-changing
implementation details such as the exact pass order or a complete source-file
map.

Human-oriented rationale and examples live in [README.md](./README.md).
Deferred work and known gaps live in [PUNCHLIST.md](./PUNCHLIST.md).


## What Silica is

Silica is Rust-inspired, with three central differences:

1. Substructural types are first-class: linear, affine, relevant, and
   unrestricted usage are selected through `Copy` and `Drop`.
2. Values are immovable by default. Bitwise relocation requires `Move`.
3. Effects are intended to build on first-class coroutines rather than
   compiler-specific iterator, async, exception, and generator machinery.

The compiler accepts the surface HLL (`.si`) and MIR (`.sim`). HLL is parsed,
checked, and lowered to MIR; both inputs then use the MIR pipeline. The backend
emits textual LLVM IR.

The exact implemented feature set changes frequently. Consult code, fixtures,
and `PUNCHLIST.md` rather than maintaining a second status list here.

## Stable compiler contracts

- HLL is expression-oriented; MIR is an explicit CFG of basic blocks.
- MIR makes value use explicit through `copy`, `move`, and pre-elaboration
  `take` operands.
- Elaboration makes implicit ownership transitions explicit, notably with
  `unborrow` and `drop`.
- Checkers validate MIR without silently repairing the property they check.
- The elaborated MIR is the canonical artifact pinned by ordinary success
  fixtures.
- MIR functions return through `&out` parameters; MIR function types have no
  result position.
- Lifetime loans and pointee initialization obligations are separate analyses:
  lifetime checking decides whether access conflicts with an active loan;
  place-state checking decides whether the pointee is in the required state.
- Function and type signatures live in the type environment; bodies remain in
  the program being analyzed and elaborated.
- Monomorphization occurs after semantic checking, at the codegen boundary.
- Raw pointers opt out of safe-reference guarantees: they create no loan and
  dereference does not prove initialization, lifetime, or alias safety.

For the exact current ordering and error-recovery behavior, read
`src/lib.rs`; do not reproduce its pass list here.


## Sources of truth

When documentation and implementation disagree, use these authorities:

- Pipeline order and pass interaction:
  [`src/lib.rs`](./src/lib.rs), especially `lower_hll_to_mir`,
  `check_mir_without_elaboration`, and `elaborate_and_check_mir`.
- Accepted syntax:
  [`tree-sitter-silica/common/grammar.js`](./tree-sitter-silica/common/grammar.js),
  [`tree-sitter-silica/hll/grammar.js`](./tree-sitter-silica/hll/grammar.js),
  and [`tree-sitter-silica/mir/grammar.js`](./tree-sitter-silica/mir/grammar.js).
- HLL and MIR data models:
  [`src/hll/ast.rs`](./src/hll/ast.rs),
  [`src/mir/ast.rs`](./src/mir/ast.rs), and
  [`src/common.rs`](./src/common.rs).
- Fixture selection, output rendering, and golden-file updates:
  [`tests/fixtures.rs`](./tests/fixtures.rs).
- Current user-visible behavior: fixture inputs and their expected siblings.
- Intended semantics and rationale: [README.md](./README.md).
- Deferred or incomplete behavior: [PUNCHLIST.md](./PUNCHLIST.md).

Do not infer current behavior from stale prose when the relevant code or
fixture can answer directly.

## Substructural semantics

`Copy`, `Drop`, and `Move` are independent capabilities:

| Markers | Repeated use | May forget | Bitwise move |
|---|---:|---:|---:|
| none | no | no | no |
| `Copy` | yes | no | no |
| `Drop` | no | yes | no |
| `Move` | no | no | yes |
| `Copy + Drop` | yes | yes | yes, implied |
| `Copy + Move` | yes | no | yes |
| `Drop + Move` | no | yes | yes |
| `Copy + Drop + Move` | yes | yes | yes; explicit `Move` is redundant |

The only implemented blanket implication is:

```text
Copy + Drop → Move
```

Higher-tier traits such as `Clone`, `Destroy`, or `Transfer` may appear in
design prose but are not part of the current marker representation.

For aggregates, a declared marker must be satisfied compositionally by every
field or variant payload. Arrays inherit the element class.

Generic marker bounds have two sides:

- Declaration side: a generic body is checked assuming each parameter’s
  declared bounds.
- Use side: concrete arguments must satisfy those bounds at every
  instantiation.

Together these allow the class of a valid custom-type instantiation to be read
from the declaration without substituting its arguments during `class_of`.

`Drop` currently means that a value may be explicitly consumed or forgotten.
It should not be confused with a fully implemented runtime destructor system.

## Reference obligations

A reference kind specifies both a pointee-state obligation and the markers of
the reference value itself:

| Kind | Required at creation | Required at expiry | Reference markers |
|---|---|---|---|
| `&T` | initialized | initialized | `Copy + Drop + Move` |
| `&mut T` | initialized | initialized | `Drop + Move` |
| `&out T` | uninitialized | initialized | `Move` |
| `&drop T` | initialized | uninitialized | `Move` |
| `&uninit T` | uninitialized | uninitialized | `Drop + Move` |

`&mut` and `&uninit` preserve pointee state. `&out` and `&drop` change it and
therefore carry an obligation that cannot be forgotten. The obligation moves
with the reference value.

HLL borrow expressions spell the `&drop` operation as `&deinit expr`; MIR uses
`&drop place`. The reference type remains `&drop T`.

## Initialization state

Every tracked owned place has one of these states:

| State | Meaning |
|---|---|
| `NeverInit` | Declared but never written |
| `Init` | Fully initialized and readable |
| `Moved` | Previously initialized, then consumed |
| `Partial` | Aggregate descendants have different states |
| `Diverged` | CFG predecessors disagree about the state |

Important consequences:

- Reads require `Init`.
- Writing every aggregate leaf folds `Partial` to `Init`.
- Consuming every aggregate leaf leaves the aggregate uninitialized.
- `NeverInit` and `Moved` both satisfy an “uninitialized” precondition.
- `Diverged` is not silently accepted by later checks.
- Returning normally requires every owned value to have been consumed.
- `abort` and `unreachable` have no returning continuation and therefore do
  not require caller-observable cleanup.

A dynamic array index has no stable move-path identity. Consequently:

- `copy`, shared borrow, and `&mut` are permitted only when the containing
  state proves the selected element initialized.
- `&uninit` is permitted only when the containing state proves the selected
  element uninitialized.
- `move`, `drop`, assignment, `&out`, and `&drop` through a dynamic index are
  forbidden.
- Replacement at a runtime index goes through a state-preserving mutable
  reference.

## Syntax orientation

The following BNF is a compact reading guide, not the parser specification.
The Tree-sitter grammars named under “Sources of truth” are authoritative.

### Shared declarations and types

```text
program       = declaration*

declaration   = struct_decl | enum_decl | function_decl

markers       = ":" marker ("+" marker)*
marker        = "Copy" | "Drop" | "Move"

type_params   = "<" generic_param ("," generic_param)* [","] ">"
generic_param = identifier [markers]
              | lifetime [":" lifetime ("+" lifetime)*]

type_args     = "<" (type | lifetime) ("," (type | lifetime))* [","] ">"

type          = integer_type | float_type | "bool" | "unit" | "never"
              | identifier [type_args]
              | "&" [lifetime] type
              | "&mut" [lifetime] type
              | "&out" [lifetime] type
              | "&drop" [lifetime] type
              | "&uninit" [lifetime] type
              | "*" type
              | "[" type ";" integer_literal "]"
```

### MIR

```text
struct_decl   = "struct" [type_params] identifier [markers]
                "{" (field [","])* "}"

enum_decl     = "enum" [type_params] identifier [markers]
                "{" (variant [","])* "}"

function_decl = ["extern" [abi_string]] "fn" [type_params] identifier
                "(" params ")"
                (";" | "{" local* basic_block* "}")

local         = identifier ":" type ";"
basic_block   = identifier ":" (statement ";")* terminator [";"]

place         = identifier
              | place "." identifier
              | place "as" identifier
              | place ".*"
              | place "[" operand "]"

operand       = "copy" place
              | "move" place
              | "take" place
              | constant

rvalue        = operand
              | "&" place | "&mut" place | "&out" place
              | "&drop" place | "&uninit" place | "&raw" place
              | identifier [type_args] "::" identifier "(" operand ")"
              | "[" operands "]"
              | "ptr_cast" "(" operand "," type ")"

statement     = place "=" rvalue
              | "call" operand "(" operands ")"
              | "drop" place
              | "unborrow" place
              | "require_uninit" place

terminator    = "goto" identifier
              | "return"
              | "branch" "(" operand ")"
                "[" "true:" identifier "," "false:" identifier "]"
              | "switchEnum" "(" place ")" "[" switch_cases "]"
              | "abort"
              | "unreachable"
```

MIR syntax traps:

- The first basic block is the entry block.
- Local declarations precede all basic blocks.
- MIR functions and function types have no return arrow.
- Return values use an `&out` parameter, conventionally `$return`.
- `call` is a statement, not an rvalue.
- `switchEnum` takes a place because each outgoing edge refines that place.
- `take` is resolved during elaboration; downstream MIR must contain only
  explicit `copy` and `move`.
- `require_uninit` is a checked ghost assertion, not a consume operation.
- `$`-prefixed identifiers are reserved for compiler and intrinsic names.

### HLL

```text
function_decl = ["extern" [abi_string]] ["unsafe"] "fn" [type_params]
                identifier "(" params ")" ["->" type]
                (";" | block)

statement     = "let" ["mut"] identifier [":" type] ["=" expression] ";"
              | "defer" expression ";"
              | expression ";"
              | block_like_expression

expression    = assignment
              | binary_expression
              | unary_expression
              | borrow_expression
              | postfix_expression
              | literal
              | identifier
              | block | "if" | "loop"
              | "break" [expression]
              | "continue"
              | "return" [expression]
              | struct_constructor
              | enum_constructor
              | array_literal

postfix       = expression "." identifier
              | expression ".*"
              | expression "as" type
              | expression "(" arguments ")"
              | expression "[" expression "]"
              | expression "match" "{" arms "}"
```

HLL syntax traps:

- Blocks evaluate to their trailing expression; no trailing expression means
  `unit`.
- `if`, `loop`, `match`, and blocks are expressions.
- `match` is postfix: `value match { ... }`.
- Dereference is postfix: `value.*`.
- Arithmetic and comparison expressions lower through compiler intrinsics.
- Assignment requires a mutable binding, except that writing through a
  reference does not reassign the reference binding itself.
- An uninitialized `let` requires enough type information to determine its
  type.
- `$`-prefixed identifiers are forbidden in HLL.
- If a surface feature cannot preserve the MIR shape needed by a test, write
  that test directly in `.sim` and document why.

## Canonical language examples

Prefer executable, fixture-backed examples over programs copied into prose.

Useful starting points include:

- [`tests/programs/heap_linked_list_of_i64.si`](./tests/programs/heap_linked_list_of_i64.si)
  for aggregates, raw pointers, mutation, loops, calls, and ownership.
- [`tests/programs/enum_matches.si`](./tests/programs/enum_matches.si)
  for enum construction and postfix matching.
- [`tests/programs/arithmetic_and_casts.si`](./tests/programs/arithmetic_and_casts.si)
  for operators, scalar types, inference, and casts.

When adding a canonical example, make it a normal fixture first and link to it
from documentation. Do not maintain a second untested copy.

## Testing discipline

Fixture tests are the primary test surface for “program in, artifact out.”
Prefer a fixture over a pass-internal unit test whenever the behavior is
observable end to end.

Fixture selection is convention-based:

| Input and location | Pipeline | Expected artifact |
|---|---|---|
| `foo.si` or `foo.sim` | Full lowering/check/elaboration | `foo.expected.sim` or `foo.err.expected` |
| `foo.preelaborated.sim` | Check without ownership elaboration | `foo.preelaborated.expected.sim` or `.err.expected` |
| `tests/codegen/foo.sim` | Full pipeline plus codegen | `foo.expected.ll` |
| `tests/codegen-raw/foo.sim` | Parse plus codegen, without checking | `foo.expected.ll` |

Rules:

- Prefer `.si` when the behavior can be expressed faithfully in HLL.
- Use `.sim` for exact CFG shapes, explicit ownership operations, lifetime
  forms lost by HLL lowering, or MIR-only features.
- Prefer extending a dense success/failure fixture pair over creating many
  one-case files.
- Every new diagnostic code needs a negative fixture that pins its complete
  rendered output.
- Pair positive behavior with the corresponding negative boundary.
- Add `# covers:` comments to fixture functions to identify the semantic cell
  being exercised. This is a review convention, not runner-enforced metadata.
- Use unit tests for private pass invariants, fixed-point behavior, parser
  internals, or intermediate forms that the full pipeline intentionally
  rewrites.

`cargo run` is useful for inspecting one program, but its CLI rendering is not
the fixture renderer. Golden comparison is owned by `tests/fixtures.rs`.

`UPDATE_EXPECT=1 cargo test --test fixtures` rewrites every fixture expectation
and removes a stale success/error sibling when a fixture changes category.
Run it only in a known-quiescent working copy. Never run it concurrently with
other agents editing fixtures.

## Grammar changes

Edit `grammar.js`, not generated parser artifacts. Regenerate both grammars:

```bash
for lang in hll mir; do
    (cd "tree-sitter-silica/$lang" && tree-sitter generate)
done
```

Generated artifacts include `src/parser.c`, `src/grammar.json`, and
`src/node-types.json`. Include their changes with the grammar edit.

## Change audits

When extending a compiler-internal enum, find every dispatch rather than
trusting a maintained file list:

```bash
rg -l 'TypeKind::' src
rg -l 'PathStep::' src
rg -l 'RefKind::' src
rg -l 'Operand::' src
rg -l 'InitState::' src
```

Audit parser, pretty-printer, helpers, type checking, dataflow passes,
elaborators, monomorphization, layout, and codegen as applicable.

In checker and elaboration code, every wildcard arm, early-returning
`let ... else`, or `else { continue; }` over compiler state must either be
exhaustive or carry a comment explaining exactly why skipped variants are
irrelevant. Adding an enum variant requires re-reading those arguments.

`Env::field_type` resolves struct fields only. Array indexing must dispatch on
`TypeKind::Array` and use the element type explicitly.

Diagnostic codes live in per-pass enums. Adding a code to an existing pass
normally changes that pass and its fixtures; the central `DiagCode` changes
only when introducing a new diagnostic family.

## Version control
This repository uses Jujutsu (jj) for working-copy operations. Do not use
Git commands to rewrite or discard work.
Common commands:
jj status
jj diff
jj log
jj describe -m "description"
jj new
jj split PATHS...
Preserve unrelated working-copy changes. Do not regenerate all golden files
while another agent is modifying fixtures.