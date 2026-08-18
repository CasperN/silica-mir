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

Silica is heavily Rust-inspired, with three central differences:

1. Substructural types are first-class: linear, affine, relevant, and
   unrestricted types are supported and selected through special traits.
2. Values are immovable by default and opt-in via a `Move` trait.
3. Effects are (planned to be) built on first-class coroutines rather than
   compiler-specific iterator, result, option, async, exception, and generator
   machinery.

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
- MIR functions return through a trailing `$return: &out R` parameter at the
  decl level. Fn types uniformly carry a `has_return_param: bool` flag rather
  than a separate result position; when set, the trailing `&out R` in `params`
  is semantically the return channel, and codegen picks sret or register-return
  based on the fn's ABI.
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

- Pipeline order and pass interaction: [`src/lib.rs`](./src/lib.rs).
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

## Substructural types

Values in Silica are linear. Relaxations are provided by the `AutoDrop` and
`AutoClone` traits, which tell the compiler that the type may be used fewer
than 1 and greater than 1 times respectively. Scalar types are both `AutoDrop`
and `AutoClone` so they can be used freely.

The substructural system applied to a given value comes from the traits on the
value's type:

| Trait                   | substructure | may use twice | may be forgotten |
|-------------------------|--------------|---------------|------------------|
| (none)                  | linear       | no            | no               |
| `AutoDrop`              | affine       | no            | yes              |
| `AutoCopy`              | relevant     | yes           | no               |
| `AutoCopy + Auto Drop`  | unrestricted | yes           | yes              |

Substructural types typically only track how many times a value can be used.
However, Silica has twelve traits that track whether a value may be
copied, moved, or destroyed; and how trivially or explicitly that happens.

| Implementation         | `Copy`      | `Drop`        | `Move`           |
|------------------------|-------------|---------------|------------------|
| Trivial (bitwise)      | `Copy`      | `Drop`        | `Move`           |
| Pure and implicit      | `AutoClone` | `AutoDestroy` | `AutoTransfer`   |
| Pure and explicit      | `Clone`     | `Destroy`     | `Transfer`       |
| Effectful and explicit | `CoClone`   | `CoDestroy`   | `CoTransfer`     |

* `Copy` and `Move` are bitwise operations, `Move` marks the original place as
logicially deinitialized. Similarly `Drop` is a no-op deinitialization.
* `Clone`, `Destroy`, and `Transfer` require non-trivial but pure methods to
duplicate, destroy, or move an object.
* The `Auto*` variants allow the compiler to implicitly call those methods to
help programs typecheck. This is useful for passing reference counted pointers,
where easy sharing is the intent. 
* The `Co` variants may perform algebraic effects when invoked. E.g. for
asynchronous object destruction.
* **Rust comparison:** `Copy` and `Move` are analogous between Rust and Silica,
  but Rust's `Drop` is more like Silica's `AutoDestroy` - customizable and
  implictly inserted.
* Blanket implementations:
  * Each row in the table has a blanket implementation for the following row.
    E.g. all types that are `Copy` are also `CoClone` and all types that are
    `AutoDestroy` are also `Destroy`. 
  * The compiler derives default implementations so `T: Copy + Drop` imply
    `T: Move`, `T: Clone + Destroy` imply `T: Transfer`, etc. This default
    implementation may be overridden, e.g. to remove an intermedediate value. 
  * Because the last two rules can be applied repeatedly, `T: Copy + Destroy`
    imply `T: CoTransfer`.

The trivial and auto-tier traits require compiler support, as they are implicit.
The explict versions are (planned to be) implemented in the standard library.


## Reference obligations

A reference kind specifies both a pointee-state obligation and the markers of
the reference value itself:

| Kind        | At creation   | At expiry     | Structural Traits    |
|-------------|---------------|---------------|----------------------|
| `&T`        | initialized   | initialized   | `Copy + Drop + Move` |
| `&mut T`    | initialized   | initialized   | `Drop + Move`        |
| `&out T`    | uninitialized | initialized   | `Move`               |
| `&drop T`   | initialized   | uninitialized | `Move`               |
| `&uninit T` | uninitialized | uninitialized | `Drop + Move`        |

The initialization state of `&mut` and `&uninit` are preserved at the start and
end of the borrow. `&out` and `&drop` are obliged to change the state and
therefore cannot be forgotten (`!Drop`). As with Rust, `&T` is `Copy` because
multiple immutable references are okay.

Both HLL and MIR spell the drop borrow operation as `&drop expr` / `&drop place`.
The reference type is `&drop T`.

## Initialization state

The MIR analyzes the initialization state of every place in the program. Every
tracked owned place has one of these states:

| State       | Meaning                                     |
|-------------|---------------------------------------------|
| `NeverInit` | Declared but never written                  |
| `Init`      | Fully initialized and readable              |
| `Moved`     | Previously initialized, then consumed       |
| `Partial`   | Aggregate descendants have different states |
| `Diverged`  | CFG predecessors disagree about the state   |

Important consequences:

- Reads require `Init`.
- Writing every aggregate leaf folds `Partial` to `Init`.
- Consuming every aggregate leaf folds it to `Uninit`.
- `NeverInit` and `Moved` both satisfy an “uninitialized” precondition.
- `Diverged` states are not statically known is rejected by checks that require an initialization state precondition.
- Returning from a function requires every owned value to be uninitialized - though drop_elaboration may insert those.
- `abort` and `unreachable` do not trigger exit cleanup. Cleanup required at
  an earlier semantic program point still occurs.

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
              | "&" [lifetime] "mut" type
              | "&" [lifetime] "out" type
              | "&" [lifetime] "drop" type
              | "&" [lifetime] "uninit" type
              | "*" type
              | "[" type ";" integer_literal "]"
```

### MIR

```text
struct_decl   = "struct" identifier [type_params] [markers]
                "{" (field [","])* "}"

enum_decl     = "enum" identifier [type_params] [markers]
                "{" (variant [","])* "}"

function_decl = ["extern" [abi_string]] "fn" identifier [type_params]
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
- To return `R` add a `$return: &out R` final call parameter.
- `call` is a statement, not an rvalue.
- `switchEnum` takes a place because each outgoing edge refines that place.
- `take` is resolved during elaboration; downstream MIR must contain only
  explicit `copy` and `move`.
- `require_uninit` is a checked ghost assertion, not a consume operation.
- `$`-prefixed identifiers are reserved for compiler and intrinsic names.

### HLL

```text
function_decl = ["extern" [abi_string]] ["unsafe"] "fn" identifier [type_params]
                "(" params ")" ["->" type]
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
  one-case files. Survey existing tests with `tree -I "*.expected*" tests/`
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
```bash
jj status
jj diff
jj log
jj describe -m "description"
jj new
jj split PATHS...
```
Preserve unrelated working-copy changes. Do not regenerate all golden files
while another agent is modifying fixtures. Prior to starting work, use
`jj status` to confirm existing changes.

## Rejecting feature work as not-yet-ready.
Often a new feature requires a dependent feature or cleanup to be implemented
cleanly and without hacks. Reject feature work if prerequisite maintainability
passes are required to implement the new feature correctly and without
compromises to long term quality. Reject feature work even if the prerequisite
was discovered in the middle of a change. Escalate for direction or
use `jj` to land the maintainability pass upstream of the feature change.

If a desired feature or cleanup is nice-to-have but should not block the current
feature work, mark it with a TODO or add it to the punchlist.

## Pre-commit check
Before commiting, please execute the following steps, step by step, one at a time. If changes have to be made, redo the entire pre-commit check. If feeling lazy, delegate these checks to a subagent.

1. Review the current change for correctness, maintainability, and simplicity. Be skeptical of incomplete matches, `expect`, `unwrap`, and other code that smells of partial implementations.
2. Reject work as incomplete if they are hacky or contain shortcuts. Sacrifices to long term correctness and rigor has cost the project more time than any shortcut has saved. 
3. Reject work as incomplete if a feature is not fully implemented, e.g. if there are missing cases, unhandled interactions, or caveats to completeness.
4. Reject work as incomplete if any TODO or punchlist item is sufficiently related or small be folded into this commit.
5. Review changes to test fixtures for totality of test coverage. Every new feature needs to be tested against every existing feature it may interact with. Every feature interaction requires a success case (that passes compilation) and at least one error case.
6. Remove any unit-tests that are redundant with end-to-end tests under `tests/`, or if they may be implemented as end-to-end tests, rewrite them as such.
7. Combine any small end-to-end test fixtures into an existing large test fixture or a new large test fixture if there are sufficient related cases. See the Testing Discipline rules.
8. Remove any references to session-specific enumerations, so they do not get stored in the durable commit history. E.g. "arc-1", "task-1", "pass-1", etc. Future work may be marked with TODO comments
9. Discuss any newly introduced jargon, vocabulary, or terms-of-art. All words used in code or comments must be either common words that are seen in every compiler and obvious from context, or are defined in the Silica README. Prefer to use existing terminology where possible, even if reusing existing terms would be more verbose. New jargon that is visible across multiple files, e.g. both tests and feature code, is especially dangerous.
10. Remove any comments that are obvious from the surrounding code. Only facts that are NOT inferrable from the code should be recorded in comments.
11. Remove or relocate any comments that are irrelevant to the surrounding code, e.g. referencing how a different system works when the current file does not otherwise mention that system.
