# AGENTS.md

Agent-facing reference for the Silica-MIR compiler. Read this first
if you're an agent editing or auditing the repo — the file is the
cross-tool convention (Codex, Cursor, Antigravity, Claude Code).
Human tutorial and semantic prose live in [README.md](./README.md);
deferred work in [PUNCHLIST.md](./PUNCHLIST.md).

## What Silica is

Heavily Rust inspired, but with three deliberate departures:
(1) **substructural types beyond affine** — linear, affine, relevant,
and unrestricted are all first-class, selected via `Copy`/`Drop`
marker combinations;
(2) **immovable-by-default values** that opt into bitwise moves via
a `Move` marker (coroutines can hold self-references without pinning);
(3) **algebraic effects via first-class coroutines** — iterators,
async, exceptions, generators become library features on one
`Co<T ! E>` primitive.

This crate is the checker + MIR + LLVM codegen. It parses either the
surface HLL (`.si`) or the MIR (`.sim`) directly, runs a shared
pipeline (type-check, substructural, init-state, NLL, drop-elab,
lifetime), and emits textual LLVM IR. Coroutines and effects are
deferred behind current work; substructural + immovable + regions +
generics are landed.

## Compiler map

```
src/lib.rs                  Pipeline entry: `elaborate_and_check_mir`
src/main.rs                 CLI + diagnostic rendering
src/common.rs               Lifetime, Marker, Markers, RefKind, Span
src/diagnostics.rs          Diagnostic + DiagCode aggregator
src/hll/parser.rs, ast.rs   HLL frontend (tree-sitter CST → HLL AST)
src/hll/type_check.rs       HM-style inference on HLL AST
src/hll/mut_check.rs        `let mut` enforcement
src/hll/lowering.rs         HLL AST → MIR CFG (materializes $return, if/match to CFG)
src/mir/parser.rs           MIR frontend (tree-sitter CST → MIR AST)
src/mir/ast.rs              MIR types, places, operands, statements, terminators
src/mir/pretty_print.rs     Elaborated-MIR renderer used by fixture tests
src/mir/type_check/         Declarations, stmt/rvalue/place typing, generic bounds
src/mir/substructural/      Marker composition (`class_of`) + stmt-level Copy/Move
src/mir/place_state/        Init lattice, ref obligations, copy-relax, drop-elab
src/mir/lifetime/           Regions, loans, NLL, elision, outlives constraint solver
src/mir/variant_flow.rs     Enum refinement + switchEnum exhaustiveness
src/mir/block_reachability.rs   Dead-block warnings
src/mir/codegen/            LLVM IR emission (assumes MIR is well-checked)
src/mir/dataflow.rs         Shared fwd/bwd CFG framework
src/mir/cfg_edit/           split_edge and other CFG rewrites
src/mir/mono/               Monomorphization (post-check, pre-codegen)

tests/<pass_or_feature>/    Fixture dirs. See "Fixture writing" below.
tests/fixtures.rs           Fixture runner (single `all_fixtures` test).
tree-sitter-silica/         Grammar. Common rules in common/grammar.js.
                            Regenerate: `cd tree-sitter-silica/{hll,mir}
                            && tree-sitter generate`
```

## Pipeline order (from `elaborate_and_check_mir`)

Pre-elab checks → elaboration → post-elab checks:

1. `type_check` — declarations, stmt/rvalue/place typing, generic bounds.
2. `substructural::composition` — decl-side marker consistency.
3. `layout::check_sizes_finite` — reject by-value recursion.
4. `substructural::check` — stmt-level Copy/Move enforcement.
5. `variant_flow` — switchEnum exhaustiveness + variant refinement.
6. `block_reachability` — dead-block warnings.
7. **`copy_relaxation`** — `take` → `move`/`copy` based on demand.
8. **`nll`** — insert `unborrow` at last-use.
9. **`drop_elaboration`** — insert `drop` before returns for Init-at-return Drop values.
10. `place_state::check` — init lattice + ref obligations on elaborated MIR.
11. `lifetime::check` — loans + outlives constraints on elaborated MIR.

Elaboration passes (7–9) run only if pre-elab is error-free. Post-elab
checks (10–11) validate the canonical elaborated form.

## Load-bearing invariants when editing

1. **Silent-fallthrough discipline.** Every `_ => {}`, `let ... else { return; }`,
   or `else { continue; }` in `src/mir/{place_state,lifetime,substructural,type_check,variant_flow}`
   must exhaustive-match or carry a comment justifying the fallthrough.
   Adding a new `TypeKind` / `PathStep` / `RefKind` / `InitState` /
   `Operand` variant is a trigger to re-audit these sites.

2. **`env.field_type` only handles struct fields.** For arrays, dispatch
   on `TypeKind::Array` separately and use the element type. Three
   soundness bugs lived in walks that missed this.

3. **`class_of(Custom(_, args))` is decl-side + use-site duality.** The
   decl body was verified assuming declared bounds; use sites verify
   the args satisfy those bounds. No substitution required for class-of.

4. **Blanket implications**: `Copy + Drop → Move`, `Clone + Destroy → Transfer`,
   etc. Implemented in `Markers::implies` in `src/common.rs`. Overridable
   by explicit declaration.

5. **`Region::Static` corresponds to `Lifetime("static")`.** The special
   name check is `lt.0 == "static"` (Lifetime is a tuple struct around
   String). `'static` is reserved and cannot be declared as a user
   lifetime param.

## Fixture writing

### Layout
- `tests/<topic>/<name>.sim` + `<name>.expected.sim` — success case;
  compares pretty-printed **elaborated** MIR.
- `<name>.sim` + `<name>.err.expected` — expects diagnostics; compares
  rendered output with source-snippet caret.
- `<name>.preelaborated.sim` + `<name>.preelaborated.expected.sim`|`.err.expected`
  — validates already-elaborated MIR without re-running NLL/place-state
  elaboration.
- `tests/codegen/foo.expected.ll` — full pipeline + codegen → LLVM IR.

### Rules
- **Prefer extending existing fixture files** to creating new ones.
  Density > file count. Consolidate opportunistically.
- **HLL (.si) over MIR (.sim)** when both work — exercises lowering
  too.
- **Every DiagCode has a negative fixture** pinning its rendered output.
- **Every positive fixture pairs with a negative fixture** for the rule's
  other side.
- **`# covers:` tag on each fn**: `# covers: type_kind=X ref_kind=Y op=Z class=W ...`
  per the feature-list axes in README §Testing discipline.

### Running as a subagent
- Write .sim files with `Write`.
- Capture actual compiler output per case with
  `cargo run --quiet --bin silica-mir -- <file>`. Report a table
  (cell | expected | actual | ✅ / ❌) back to the parent.
- **DO NOT run `UPDATE_EXPECT=1 cargo test`.** The parent will
  regenerate all expected files at a known-quiescent state. If you
  run it mid-fanout, you may bless another concurrent agent's
  incomplete fixture state.

### Feature-list axes for `# covers:`
- `type_kind`: scalar, shared_ref, exclusive_ref, raw_ptr, struct, enum, array, nested_aggregate, param
- `ref_kind`: shared, mut, out, drop, uninit
- `class`: L, C, D, M, CD, CM, DM, CDM (subsets of {Copy, Drop, Move})
- `op`: copy, move, drop, borrow, unborrow, deref_read, deref_write, call_arg, assign_target, return
- `init`: NeverInit, Init, Moved, Partial, Diverged
- `cfg`: straight, if, match, loop
- `boundary`: intra_fn, call, return_out, extern
- `lifetime_bound`: unbounded, single_outlives, chain, cyclic, diamond, static_lhs, static_rhs, etc.

## Common pitfalls

- **MIR fns have no return arrow.** Returns go through `&out $return`
  parameters. `fn foo() -> R` is HLL syntax only; MIR is
  `fn foo($return: &out R)`.
- **HLL doesn't propagate user-written `'a` on `Ref` types** through
  `lower_type` today. Test outlives bounds via `.sim` files, not `.si`.
  See punchlist "HLL Ref-type lifetime passthrough."
- **`$return` isn't visible in HLL bodies.** In HLL you return by making
  the block's trailing expression the return value; the lowering
  materializes `$return.* = <expr>`.
- **MIR grammar quirks**: struct/enum field separators are
  whitespace-or-comma (not required); HLL is comma-required. Function
  bodies use blocks with `label:` headers and terminators like `return`,
  `goto label`, `branch(op) [true: l1, false: l2]`, `switchEnum(place)
  [V1: l1, V2: l2]`, `abort`, `unreachable`.
- **`drop`/`move`/`copy`/`&out`/`&drop` on a dynamic-index target**
  (`a[copy i]`) are rejected. Slot replacement at a dynamic index goes
  through `p = &mut a[i]; drop p.*; p.* = new;`.
- **Version control uses `jj`, not `git`.** Common commands: `jj log`,
  `jj status`, `jj diff`, `jj describe -m "..."`, `jj new`, `jj split
  PATHS...`.

## When to audit which files

When adding this feature | Grep + review these dispatches
--- | ---
New `TypeKind` variant | `src/mir/{place_state,lifetime,substructural,type_check,variant_flow,drop_elaboration}.rs` — search `match .*ty.kind\|match &ty\.kind` and update every exhaustive/wildcard match.
New `PathStep` variant | Same set; search `match.*step\|PathStep::`.
New `RefKind` | Same + `src/mir/lifetime/*` for loan-conflict matrix.
New `Operand` variant | `apply_operand_move`, `check_operand_read`, `operand_place`, copy_relaxation dispatch sites.
New `InitState` variant | `place_state/analysis.rs` `join_state`, `canonicalize`, `read_at`, `write_at`, `move_at`, `find_return_leaks`, `walk_overwrite_leaves`.
New DiagCode | Add positive + negative fixture; extend the corresponding module's enum with a doc-comment.

## Grammar (denormalized for grep)

### MIR (`tree-sitter-silica/mir/grammar.js`)

```
place =
    | var
    | place.field
    | place as Variant
    | place.*
    | place[operand]

operand =
    | copy place | move place | take place
    | const

rvalue =
    | operand
    | & place | &mut place | &out place | &drop place | &uninit place
    | &raw place
    | Name::Variant(operand)
    | [operand, ...]

statement =
    | place = rvalue
    | call operand ( operand, ... )
    | drop place
    | unborrow place

terminator =
    | goto label
    | return
    | branch(operand) [ true: label, false: label ]
    | switchEnum(place) [ Variant: label, ... ]
    | abort
    | unreachable

markers     = : marker (+ marker)*     # marker ∈ {Copy, Drop, Move}
type_params = < param (, param)* [,] >
param       = type_param | lifetime_param
type_param  = identifier [markers]
lifetime_param = 'ident [: 'ident (+ 'ident)*]     # outlives bounds inline
type_args   = < type (, type)* [,] >

function =
    | extern fn name ( var: type, ... ) ;
    | fn [type_params] name ( var: type, ... ) { (var: type ;)* basic_block* }

struct_decl = struct [type_params] identifier [markers] { (field: type)* }
enum_decl   = enum   [type_params] identifier [markers] { (Variant: type)* }
```

### HLL (`tree-sitter-silica/hll/grammar.js`)

Same top-level structure. Key differences:
- Expression-oriented: `if`, `match`, `loop`, blocks all evaluate to
  values.
- Postfix `match`: `expr match { arm, ... }`.
- Postfix deref: `expr.*` (borrowed from Zig).
- `&deinit T` (surface spelling for MIR's `&drop T`).
- Function types have return arrows: `fn(T,...) -> R`.
- No `$return` — trailing expr of the body is the return value.

See README §HLL Grammar for the full HLL grammar and §HLL Notes for
lowering rules.

## Semantics (denormalized)

Full prose and worked examples live in README §Semantics. Below is the
tight reference agents grep repeatedly.

### Init-state lattice

Every place carries one of:

| state       | meaning                                                       |
|-------------|---------------------------------------------------------------|
| `NeverInit` | Declared, never written.                                       |
| `Init`      | Fully written; readable.                                       |
| `Moved`     | Written, then consumed by `move` or `drop`.                    |
| `Partial`   | Per-field/per-slot state for structs and arrays.               |
| `Diverged`  | CFG join found predecessors that disagreed. Fails every check. |

- Reads (`copy`, `switchEnum`, most borrows) require `Init`.
- Writing every field folds `Partial` → `Init`; consuming every field folds it to `Moved`.
- `Uninit` shorthand = `NeverInit ∨ Moved`.
- Dynamic-index places (`a[i]` where `i` isn't a constant) have no stable identity: `move`/`drop`/state-changing borrows are rejected; only reads and state-preserving borrows on uniformly-Init arrays are allowed.

### Reference (cur, post) obligations

| kind      | current   | post      | class (substructural)   |
|-----------|-----------|-----------|-------------------------|
| `&`       | `Init`    | `Init`    | Copy + Drop (unrestricted) |
| `&mut`    | `Init`    | `Init`    | Drop, not Copy (affine)   |
| `&out`    | Uninit    | `Init`    | linear (neither)          |
| `&drop`   | `Init`    | Uninit    | linear (neither)          |
| `&uninit` | Uninit    | Uninit    | Drop, not Copy (affine)   |

- `&mut` / `&uninit` are state-**preserving** — the pointee's init state
  is unchanged from creation to expiry, so the ref itself is `Drop`.
- `&out` / `&drop` are state-**changing** — the outstanding obligation
  can't be forgotten, so the ref is linear.
- `&T` shared carries no obligation.
- HLL surface spells `&drop` as `&deinit`; both map to `RefKind::Drop`.

### Substructural markers

Two axes: how many times a value may be used (class) and how it moves
(the twelve traits table in README §Substructural traits).

Declared markers → class:

| markers                | class        | may use ≥2 | may forget |
|------------------------|--------------|------------|------------|
| (none)                 | linear       | no         | no         |
| `Drop`                 | affine       | no         | yes        |
| `Copy`                 | relevant     | yes        | no         |
| `Copy + Drop`          | unrestricted | yes        | yes        |

Blanket implications (in `Markers::implies` at `src/common.rs`):

- `Copy + Drop → Move` (bitwise move = bitwise copy + no-op forget).
- `Copy → CoClone`, `Drop → CoDestroy`, `Move → CoTransfer`, and so on
  down the "twelve traits" table.
- Chains apply repeatedly, so `Copy + Destroy → CoTransfer`.

Composition (`class_of` in `src/mir/substructural/composition.rs`):

- A struct's declared marker `M` requires every field's type to satisfy
  `M`. Same for enum variants.
- `class_of(Array(elem, _)) = class_of(elem)`.
- `class_of(Ref(kind, _, _))` is determined by the ref kind's obligation
  table above.
- `class_of(RawPtr(_))` = `Copy + Drop + Move` (unrestricted, unsafe).

### Generic bound duality

- **Decl side.** `struct<T: Copy> Box: Copy { inner: T }` is verified
  assuming `T: Copy`. Fields of type `Param(T)` are accepted under the
  declared bound.
- **Use side.** Every `Box<X>` requires `X` to satisfy the declared
  bound at the use site.

Together these justify `class_of(Custom(_, args))` without substitution.

### Lifetime bounds

- Inline on decl type_params: `fn<'a, 'b: 'a + 'static> foo(...)`.
- Stored on `DeclMeta.outlives: Vec<(subject, must_outlive)>`.
- Consumed by `check_constraints` in `src/mir/lifetime/check.rs` via
  `transitive_closure`.
- `'static` is reserved (`Region::Static`, top of order); can appear as
  a bound target but not as a declared param name.
- Struct/enum bounds parse and scope-check but aren't yet enforced at
  construction (punchlist).

### Pipeline: what gets checked where

- **Type validity** (`type_check`) — declarations are well-formed;
  place/operand/rvalue types line up.
- **Substructural composition** (`substructural::composition`) — decl
  marker consistency.
- **Substructural stmt check** (`substructural::check`) — `copy`
  requires Copy, `move` requires Move, `drop` requires Drop.
- **Variant flow** (`variant_flow`) — switchEnum exhaustiveness +
  downcast-refinement soundness.
- **Init state + ref obligations** (`place_state::check`) — dynamic
  init tracking, ref (cur, post) enforcement, return-leak check.
- **Lifetime loans + outlives** (`lifetime::check`) — loan conflicts,
  region constraint solver.

## Testing discipline (summary)

Full spec: README §Testing discipline.

- **Fixture-first.** Program in, artifact out. Every rule has a positive
  and a negative fixture.
- **Per-pass unit tests** only for private APIs / invariants a fixture
  can't observe.
- **Utility unit tests** inline `#[cfg(test)] mod tests` for small
  helpers.
- **`# covers:` tags** on every fn; enables pairwise coverage audit.
- **`UPDATE_EXPECT=1 cargo test --test fixtures`** to rewrite all
  expected files. Do this from the parent, not from concurrent
  subagents.

## When editing feels risky

- Grep for existing fixture patterns first (`grep -rn "^fn foo_\|struct Foo" tests/`).
- If a rule's positive/negative fixtures don't exist, that's a smell —
  the rule may not be covered.
- Silent fallthroughs in state-transition passes are the highest-risk
  code shape. Audit them first when you're new to a subsystem.
