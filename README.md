# Silica
This document defines the surface Silica High-Level Language (HLL) and its
middle-level intermediate representation (MIR). The compiler parses either,
runs a shared pipeline (type-check, substructural checks, init-state, NLL
elaboration, drop elaboration, lifetime checks), and emits LLVM IR.

File-extension routing:
- `.si` — HLL source. Parsed, type-checked, and lowered to MIR before the
  MIR passes run.
- `.sim` — MIR source. Parsed and fed directly into the MIR passes.

# Background on Silica
Silica is an experimental Rust-like language that explores some choices that
Rust did not make.
- **Substructural Types:** While Rust has affine types, Silica has substructural
types, affine, linear, unrestricted and relevant.
- **Immovable types:** Unlike Rust, Silica's types are immovable by default and
opt in via a `Move` trait.
- **Algebraic Effects:** Silica uses first class coroutines and algebraic
effects, so features such as streams, iterators, generators, and async become
library features. Coroutines are deferred from the Silica-MIR for initial
implementation simplicity.

## Substructural types

Values in Silica are linear. Relaxations are provided by the `AutoDrop` and
`AutoClone` traits, which tell the compiler that the type may be used fewer
than 1 and greater than 1 times respectively. Scalar types are both `AutoDrop`
and `AutoClone` so they can be used freely.

Substructural class comes from the declaration markers:

| markers                 | class        | may use twice | may be forgotten |
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


#### Reference obligations

Like Rust, Silica has shared references — but unlike Rust, it has four
kinds of mutable reference, each pairing a required init state at borrow
creation with a required state at borrow expiry. The (cur, post) table
and the rules for pointee-state tracking live in the [Semantics section
below](#semantics).

The substructural class of each kind falls out of that obligation. `&T`
is `Copy Drop` (unrestricted). The mutable kinds are all not `Copy` to
avoid data races. `&out` and `&drop` are linear (neither `Drop` nor
`Copy`) — the outstanding obligation to initialize or deinitialize the
referent cannot be forgotten. `&mut` and `&uninit` are affine (`Drop`
not `Copy`).

## Immovable Types
The `Move` marker tells the compiler a type is bitwise-movable. Without
it, it cannot be passed by move. All scalar types are movable. If a
type is both `Copy` and `Drop`, the compiler synthesizes `Move` via
the default impl `Copy + Drop → Move` (see the Substructural traits
section below). The same rule lifts up the tiers: `Clone + Destroy →
Transfer`, `CoClone + CoDestroy → CoTransfer`, and so on. Each default
impl is overridable if the user wants a direct implementation.

## Algebraic Effects
Silica uses algebraic effects in the form of coroutines. Effects may be thought
of as checked, resumable, exceptions. Breaking that down:
- **exceptions:** Effects transfer control from a coroutine to an outer handler,
much like a try-catch block in other languages.
- **resumable:** Unlike a try-catch block, the handler may resume the coroutine
and provide a value, so a coroutine frame is not always immediately destroyed
when the "exception" is thrown.
- **checked:** The set of effects that a coroutine may perform is known at
compile time and the Silica language enforces that all effects are ultimately
handled.

Many common control flow patterns that require dedicated language features may
be modeled in libraries using algebraic effects. This includes exceptions
(obviously), async-await, and generators.


# Silica HLL examples
Example syntax and definitions

Note
```
co foo() -> T ! E
```
is sugar for
```
fn foo() -> impl Co<() -> T ! E>;
```

for common and useful effects include the following:

#### Fail
```
effect Fail<Err=()> {
  op fail: Err -> never;
}
co fn map_err<T, E1, E2, rho>(
  c: impl Co<T, Fail<E1>, rho>,
  err_fn: impl FnOnce(E1) -> impl Co<E2 ! rho>, 
) -> T ! Fail<E2>, rho {
  c handle () {
    Fail.fail(err) => {
      let e2 = err_fn(err)?;
      perform Fail.fail(e2);
    }
  }
}
```

#### Iteration
```
effect Iter {
  type Item;
  op yield: Item -> ();
}
co flat_map<T, U, rho>(
  iterator: impl Co<(), Iter<Item=T>>,
  f: impl FnMut(T) -> impl Co<() ! Iter<Item=U>, rho>
) -> () ! Iter<U>, rho {
  iterator handle () {
    Iter.yield(t) => f(t) handle () {
      Iter.yield(u) => {
        perform Iter.yield(u);
        continue(())
      }
    }
  }
}
```

#### Parse
```
enum Either<A, B> {
  left: A, right: B
}
effect Parser<Input, SaveMarker, Error> {
  // Consume some input from the input stream stream.
  op read: usize -> Input;
  // Snapshot the input stream state so it can be restored.
  op save: () -> SaveMarker;
  op restore: SaveMarker -> ();
  // Fail to parse.
  op fail: Error -> Never; 
}
co alt<
  T, U, I, S, E1, E2, rho
>(
  a: impl Co<T, Parser<I, S, E1>, rho>,
  b: impl Co<U, Parser<I, S, E2>, rho>,
) -> Either<T, U> ! Parser<I, S, (E1, E2)>, rho {
  let s = perform Parser.save();
  a_error = a handle () {
    return t => return Either::Left(t),
    Parser.fail e => break e,
    // Other effects are propagated through alt to the outer handler.
  };
  s.restore();
  b_error = b handle () {
    return u => return Either::Right(u),
    Parser.fail e => break e,
  };
  s.restore();
  perform Parser.fail((a_error, b_error));
}
```

#### Async / Await
```
effect Async<Id> {
  op await: Id -> ();
}
enum Files<'a> {
  File(usize),
  Files(&'a[Files])
}
co first_of<T, U, rho>(
  mut a: impl Co<T ! Async<Files<'suspend>, rho>> + Drop,
  mut b: impl Co<U ! Async<Files<'suspend>, rho>> + Drop,
) -> Either<T, U> ! Async<Files<'suspend>, rho> + Drop
{
  let mut a_deps, mut b_deps;
  loop {
    a = a handle {
      return t => return Either::Left(t),
      Async.await(deps), k => {
        a_deps = deps;
        k
      }
    }
    b = a handle {
      return u => return Either::Right(u),
      Async.await(deps), k => {
        b_deps = deps;
        k
      }
    }
    perform Async.await(Files::Files(&[a_deps, b_deps]));
  }
}
```

# Streaming
Algebraic effects are great because they compose nicely. Consider fetching a
paginated list of images over the network: 
```
co list_images() -> i32 ! Fail<NetworkError>, Iter<Image>, Async<FileDesc> {
  ...
}
```
This computation iterates yielding `Image`s, it can fail with a network error,
and its asynchronous - waiting on file descriptors. Contrast this with Rust
where you might choose one of the following signatures
```rust
async fn list_images1() -> Result<Iter<Item=Image>, NetworkError>;
async fn list_images2() -> Iter<Item=Result<Image, NetworkError>>;
use futures::stream::Stream;
fn list_images3() -> impl Stream<Item = Result<Image, NetworkError>>;
```
`list_images1` is wrong because the iterator should be able to fail midway
through iteration. `list_images2` at least indicates failure can happen 
midstream, but they both can only await once until the start of the stream
and cannot express that there's awaiting mid-stream too. `list_images3()`
fuses `Iter` and `Async` effects with `Stream`, which is better, but the
`NetworkError` is attached to individual items rather than the stream as a
whole so its type-legal for the stream to continue after a network error.

All this to say, These 3 kinds of control flow, falibility, iteration, and
asynchrony do not compose in Rust. 

## Substructural traits

The trivial markers (`Copy`, `Drop`, `Move`) are properties, not traits
with methods — the operations are compiler-inline (memcpy, no-op
forget, memcpy + invalidate). The higher tiers expose function shapes:

```
// Pure and explicit: the user writes the method
// (or `#[derive]` auto-generates it, giving the Auto* variants).
trait Clone {
  fn clone(&self, dst: &out Self);
}
trait Destroy {
  fn destroy(&drop self);
}
trait Transfer {
  fn transfer(&drop self, dst: &out Self);
}

// Default impl (overridable): given `Clone + Destroy`, synthesize
// `Transfer` as clone-then-destroy. User impls take precedence, so
// there's no coherence conflict — a direct `impl Transfer for T`
// wins and avoids the intermediate.
impl<T: Clone + Destroy> Transfer for T {
  fn transfer(src: &drop Self, dst: &out Self) {
    Clone::clone(&*src, dst);
    Destroy::destroy(src);
  }
}
```

The pure-and-implicit tier (`AutoClone` / `AutoDestroy` /
`AutoTransfer`) has the same method signatures; the difference is
that the compiler synthesizes the body by walking fields when the
user hasn't provided one.


## Effectful substructural traits
The effectful-and-explicit traits are the effect-polymorphic versions
of the pure-and-explicit ones. Their methods are coroutines and may
perform algebraic effects.

```
trait CoClone {
  effects E;
  co clone(&self, dst: &out Self) -> () ! E;
}
trait CoDestroy {
  effects E;
  co destroy(&drop self) -> () ! E;
}
trait CoTransfer {
  effects E;
  co transfer(&drop self, dst: &out Self) -> () ! E;
}
```

These are vocabulary traits for the standard library, not inserted
by the compiler.

# Silica's Compiler Plan
1. **Parse HLL** (`.si`) into the HLL AST via the tree-sitter grammar in
   `tree-sitter-silica/hll/`, then **lower** it to MIR — collapse
   expression-oriented control flow into a CFG of basic blocks and
   materialize return values through `&out $return` parameters. `.sim`
   inputs skip this and enter the pipeline as MIR directly.
2. **Type-check and analyze** the MIR (declarations, substructural class,
   layout, init-state, variant flow, reachability) via
   `elaborate_and_check_mir` in `src/lib.rs`.
3. **Elaborate** the MIR: insert explicit `unborrow` at NLL last-use
   points and `drop`s for values live at return. This is the "elaborated
   MIR" — fast to re-check without inference.
4. **Post-elaboration checks** re-verify init state, substructural
   discipline, and lifetime loans against the elaborated program.
5. **Codegen** to LLVM IR (`src/codegen/`). Post-codegen recheck of the
   elaborated MIR remains available and is a future step for optimization
   passes.

# HLL Spec

The HLL is the surface Silica syntax users write. It's expression-oriented
(`if`, `match`, `loop`, and blocks all evaluate to a value) and lowers to
MIR. The grammar below is the authoritative shape; the tree-sitter source
lives in `tree-sitter-silica/{common,hll}/grammar.js`.

## HLL Grammar

```
program     = declaration*
declaration = struct_decl | enum_decl | fn_decl

# Fields/variants are comma-separated with an optional trailing comma.
# Generics: `struct<T: Copy> Box: Copy { inner: T }`. The optional
# `type_params` clause sits between the keyword and the decl name and
# has the same shape as MIR.
struct_decl = struct [type_params] identifier [markers] { field , ..., }
enum_decl   = enum   [type_params] identifier [markers] { variant , ..., }
field       = identifier : type
variant     = identifier : type

# Functions: optional `-> ret_ty` (defaults to `unit`); body is a block.
# Generics: `fn<T: Copy>(x: T) -> T { ... }`.
fn_decl = fn [type_params] identifier ( param , ..., ) [ -> type ] block_expr
param   = identifier : type

markers     = : marker (+ marker)*     # marker ∈ {Copy, Drop, Move}
type_params = < type_param (, type_param)* [,] >
type_param  = identifier [markers]
type_args   = < type (, type)* [,] >

# Types — same as MIR for the shared alternatives (scalars, refs,
# raw pointers, arrays, custom names with optional type args, in-scope
# type-param references) plus HLL's function-type variant
# `fn(T,...) [-> R]` with an optional return arrow (defaults to `unit`
# when omitted). MIR's function type has no arrow because MIR returns
# go through `&out $return` parameters.
type = ...   # see MIR Types, plus `fn(T,...) [-> R]`

# Statements: `let` binding or expression-statement.
stmt = let [mut] identifier [: type] = expr ;
     | expr ;

# Blocks: any number of statements, followed by an optional trailing
# expression that is the block's value. Missing → unit.
block_expr = { stmt* [expr] }

# Expressions, loose → tight: assignment → prefix → postfix → primary.
# Every operator is a named rule so the CST nests naturally.
expr        = assign_expr | prefix
assign_expr = prefix = expr                          # right-associative

prefix = postfix
       | (& | &mut | &out | &deinit | &uninit) prefix   # borrows
       | &raw prefix                                    # raw borrow

postfix = primary
        | postfix . identifier                       # field access
        | postfix . *                                # deref
        | postfix as identifier                      # downcast
        | postfix ( expr , ..., )                    # call
        | postfix [ expr ]                           # array index
        | postfix match { arm , ..., }               # postfix match

primary = int_lit | float_lit | true | false | unit
        | identifier                                     # variable
        | ( expr )                                       # grouping / ()
        | block_expr
        | if expr block_expr [ else block_expr ]
        | loop block_expr
        | break [expr] | continue | return [expr]
        | identifier { field: value , ..., }             # struct constructor
        | identifier :: identifier ( expr )              # enum constructor
        | [ expr , ..., ]                                # array literal

arm     = pattern => expr
pattern = identifier [ ( identifier ) ]                  # Variant [ (bind) ]
```

## HLL Notes

- **Expression-oriented.** `if`, `match`, `loop`, and blocks all
  evaluate to a value. A block's value is its trailing expression
  (an `expr` with no `;`) or `unit` if there isn't one.
- **No arithmetic or comparison operators.** They go through
  intrinsic function calls (see MIR Intrinsics), so the HLL doesn't
  need to reserve `+ - * /` or comparison tokens.
- **`match` is postfix** (`expr match { ... }`), reading subject-first
  and chaining naturally with method-style calls.
- **`.*` is the postfix deref** operator (borrowed from Zig).
- **HLL spells `&deinit T` where MIR spells `&drop T`.** Same
  reference kind (`RefKind::Drop`); the surface uses a name that
  reads as "de-initialize the referent."
- **Struct constructor vs identifier + block ambiguity.** `Name { ... }`
  parses as a struct constructor only when the brace contents look
  like `field: value` fields (or the braces are empty). Otherwise
  it's an identifier followed by a block, so `if cond { let x = 1; }`
  works. Tree-sitter's dynamic conflict resolution handles both.
- **No lifetime annotations at the surface.** All reference lifetimes
  are inferred at the MIR level (NLL-style).
- **Integer literal defaulting.** Unsuffixed integer literals get
  type-variable defaults; the type checker resolves them to `i64`
  if no other constraint pins them.
- **Generics have unconditional marker bounds.** `struct<T: Copy> Box`
  requires every `Box<X>` to satisfy `X: Copy`. Conditional bounds
  (`Box<T>: Copy where T: Copy`) are deferred behind this form; the
  inline decl marker still applies. See the Semantics section for the
  decl-side + use-site duality.

# MIR Spec

## Grammar

```
place =
    | var                         # identifier; `$*` names are reserved for intrinsics
    | place.field                 # struct field projection
    | place as Variant            # enum downcast projection
    | place.*                     # deref of a reference or raw pointer
    | place[operand]              # array element indexing (const- or dynamic-index)

int_lit   = (decimal | 0x<hex> | 0b<binary>) (i8|i16|i32|i64|u8|u16|u32|u64)?
                                  # underscores allowed anywhere in digits; unsuffixed → i64
float_lit = <decimal>.<decimal> (f32|f64)?
                                  # unsuffixed → f64
byte_str_lit  = b"..."            # byte string; supports \n \t \r \0 \\ \" \' \xNN
byte_char_lit = b'...'            # single byte; same escape set as byte strings

const =
    | int_lit
    | float_lit
    | byte_str_lit                # value type [u8; N]
    | byte_char_lit               # value type u8
    | true | false
    | unit
    | fnName [type_args]          # bare identifier resolves to a function's address;
                                  # generic fns require type args at the use site

operand =
    | copy place        # bitwise copy; place must be Copy; place stays initialized
    | move place        # bitwise move; place becomes uninitialized
    | const

rvalue =
    | operand
    | & place
    | &mut place
    | &out place
    | &drop place
    | &uninit place
    | &raw place                  # raw pointer; unsafe — no loan, no obligation
    | Name::Variant(operand)      # enum construction (whole-value)
    | [operand, ...]              # array aggregate literal [T; N]

statement =
    | place = rvalue
    | call operand ( operand, ... )
    | drop place
        # Marks the place as consumed/forgotten. No-op for scalars and POD types
        # and lowers to call Drop::drop(&drop place) for custom destructors.
    | unborrow place
        # Mark the place as no longer borrowed. Inserted by the NLL pass.
        # Legal iff the reference and every reborrow derived from it has been
        # consumed or forgotten.

terminator =
    | goto label
    | return
    | branch(operand) [ true: label, false: label ]
    | switchEnum(place) [ Variant: label, ... ]
    | abort
    | unreachable

basic_block = label : (statement ;)* terminator

markers     = : marker (+ marker)*     # marker ∈ {Copy, Drop, Move}
type_params = < type_param (, type_param)* [,] >
type_param  = identifier [markers]
type_args   = < type (, type)* [,] >

function =
    | extern fn name ( var: type, ... ) ;
    | fn [type_params] name ( var: type, ... ) { (var: type ;)* basic_block* }

struct_decl =
    struct [type_params] identifier [markers] { (field: type)* }

enum_decl =
    enum [type_params] identifier [markers] { (Variant: type)* }

declaration = struct_decl | enum_decl | function

program = (declaration ;)*
```

Notes:
- `move`/`copy` is explicit on every operand so the linearity check is local and syntax-directed.
- Struct construction has **no aggregate rvalue**. Structs are initialized one field at a time via `x.field = ...`; the struct as a whole is initialized exactly when all fields are.
- Enum construction *is* whole-value (`Name::Variant(operand)`): a variant's payload and discriminant must become valid atomically.
- **Array construction may be whole-value** (`[e0, e1, ..., eN-1]`) or
  piecewise (`a[0] = ...; a[1] = ...`). Piecewise construction is
  supported for constant indices — including `&out a[k]` binding to a
  specific slot. Dynamic-index writes require the whole array to
  already be Init.
- **`switchEnum` takes a place, not an operand.** It performs a *discriminant read* — a shared-read access for conflict purposes, consuming nothing. It must be a place because each out-edge refines the type of *that specific place*, which is what justifies the downcast projection in the target block. Switching on a copied temporary would sever the connection between the discriminant tested and the place downcast. (`branch` stays operand-based: `bool` is `Copy Drop` and no refinement occurs.)
- **`abort` / `unreachable`** are terminators with no successors — runtime escape hatches. They **waive linear obligations** for code that only reaches them: elaboration passes (drop, NLL) don't insert cleanup on paths that never reach `return`, because the program dies before the caller could observe. Mixed CFGs are handled precisely — if a branch has one arm reaching `return` and one reaching `abort`, obligations are still checked on the return arm.
- **Lifetimes are inferred (NLL-style).** No lifetime annotations anywhere.
Regions are internal to the checker, derived from reference liveness.
- **Return values are modeled with `&out` parameters.** Functions have no return
type; `call` is a statement, not an rvalue. This is sret/RVO. Full Silica
has return types but lowers to this to simplify the MIR.
- **Raw pointers (`*T`, created via `&raw place`) are unsafe.** Creating a
  raw pointer does NOT create a loan; deref does not check aliasing,
  init state, or lifetime. The pointer value itself is `Copy Drop Move`.
  In the HLL, dereferencing a raw pointer (`ptr.*`) or calling an `unsafe fn`
  requires being inside an `unsafe { ... }` block or an `unsafe fn` body.
  Use for FFI, unchecked buffer access, and pointer arithmetic (once we add it).
- **Reserved `$*` namespace.** Identifiers starting with `$` are reserved
  for MIR-only names (intrinsics, compiler-generated symbols). The
  higher-level language forbids `$*` identifiers, so intrinsics can
  never be shadowed by user code.
- **`fn main` is special.** Codegen synthesizes a C-conformant
  `i32 @main()` wrapper around it. The Silica `main` may take no
  parameters (wrapper always returns 0) or a single `exit: &out i32`
  parameter (wrapper returns the value written through it). Any other
  signature is rejected at check time.

## Types

```
type =
    | unit
    | i8 | i16 | i32 | i64 | u8 | u16 | u32 | u64
    | f32 | f64
    | bool
    | never                                      # uninhabited (⊥); vacuously Copy Drop Move
    | Name [type_args]                           # struct/enum name, optionally with type args
    | Name                                       # in-scope type-param reference
    | fn(type, ...)                              # no result type; results via &out params
    | &T | &mut T | &out T | &drop T | &uninit T # safe references (loan-tracked)
    | *T                                         # raw pointer (unsafe, aliasing)
    | [T; N]                                     # fixed-size array
```
Custom-vs-Param disambiguation is scope-driven: an identifier that
names an in-scope type parameter resolves to `Type::Param`; otherwise
it resolves to `Type::Custom(name, args)`.
Notes:
- **By-value recursion is rejected** as it would require infinite size.
  Recursion through references or raw pointers is allowed (a pointer is
  bounded regardless of the pointee).
- **Scalar layout** matches natural alignment: i64/u64/f64/pointer are
  8 bytes, i32/u32/f32 are 4, i16/u16 are 2, i8/u8/bool are 1. Not
  ABI-stable.
- **Arrays lay out as `N * size_of(T)`**, aligned to `T`'s alignment.
  Init state is per-slot for constant indices (piecewise construction
  via `&out a[0]`, `&out a[1]`, ... is supported); dynamic indices
  widen to the whole array.
- **Enum layout** is `{i16 discriminant, [pad x i8], [K x lane]}` where
  `lane` is chosen so LLVM infers the enum's true alignment. Variant
  discriminant = declaration order.

## Semantics

Four rule-sets are enforced over MIR.

### Init-state

Every place carries an init state, which together form a lattice.

| state       | meaning                                             |
|-------------|-----------------------------------------------------|
| `NeverInit` | Declared, never written                             |
| `Init`      | Fully written; readable                             |
| `Moved`     | Written, then consumed by `move` or `drop`          |
| `Partial`   | Per-field state (structs / arrays / enum payloads)  |
| `Diverged`  | CFG-join found predecessors that disagreed          |

Reads (`copy`, `switchEnum`, most borrows) require `Init`. Writing every
field of a `Partial` folds it to `Init`; consuming every field folds it
to `Moved`. `Diverged` fails every check — join sites unify only when
predecessors match.

Canonical tests:
- `tests/init_state/partial_init/`,
- `tests/init_state/move_and_drop/`.

### Reference obligations

Each mutable reference kind has a `(current, post)` obligation on its
pointee at borrow creation and expiry, respectively:

| kind      | current   | post      |
|-----------|-----------|-----------|
| `&mut`    | `Init`    | `Init`    |
| `&out`    | Uninit    | `Init`    |
| `&drop`   | `Init`    | Uninit    |
| `&uninit` | Uninit    | Uninit    |

("Uninit" here means `NeverInit` or `Moved`.) The pointee state is
tracked with full `InitState` granularity, so per-field writes via
`r.*.field = ...` accumulate through `Partial` and fold to `Init` on
completion. Shared `&T` carries no obligation (it's `Copy Drop`).

For `&out` / `&uninit` on an `Init` place, drop elaboration inserts
`drop place` before the borrow if the type is `Drop`; a linear (non-Drop)
place must be moved out first.

Canonical: `tests/init_state/borrow_precondition/`, `tests/init_state/ref_obligations/`.

### Marker composition

A struct/enum's declared markers must be satisfied by every field or
variant payload. `struct Foo: Copy { r: &mut i64 }` fires
`COMP-CopyMarkerNotSatisfied` because `&mut i64` is not `Copy`. A decl
carrying both `Copy` and `Drop` reports each unsatisfied marker
independently, so one offending field can fire two diagnostics.

Canonical: `tests/substructural/composition/`.

### Generic bound duality

Bounds on generic type parameters are checked in two places:

- **Decl side.** `struct<T: Copy> Box: Copy { inner: T }` is verified
  assuming `T: Copy`. The composition check accepts fields of type
  `Param(T)` under the declared bound.
- **Use side.** Every `Box<X>` requires the argument `X` to satisfy the
  declared bound (`X: Copy`).

Together these justify `class_of(Custom(_, args))` without substitution:
the body was verified generically, and the use site verifies the args.
Monomorphization is not required for checking — only for codegen.

Canonical: `tests/generics/`.

## Compiler Structure
Where possible the compiler splits subsystems into independent passes.
`src/dataflow.rs` contains common forwards/backwards CFG traversal utilities
that are shared across multiple passes. The compiler splits elaboration and
checker passes. Elaboration passes add statements, such as `drop` and
`unborrow`, which make ownership/linearity transitions explicit. Checker passes
do not modify the instructions but verify their properties.

The authoritative pipeline is `elaborate_and_check_mir` in `src/lib.rs`.
Roughly:

Pre-elaboration checks:
1. **Type check** — declarations, statements, terminators, place / operand /
   rvalue typing.
2. **Substructural composition** — a struct/enum's declared markers must be
   consistent with its fields/variants.
3. **Layout / recursion** — reject by-value recursion; compute sizes.
4. **Substructural statement check** — `copy`/`move` require Copy/Move types.
5. **Variant flow** — `switchEnum` exhaustiveness + enum-variant refinement.
6. **Block reachability** — dead-block warnings.
7. **Init state + reference obligations** — the `(cur, post)` state machine
   over locals; also validates deref preconditions and enforces
   `&out`/`&drop` obligations.

Elaboration:

8. **NLL lifetime elaboration** — insert `unborrow` at ASAP last-use points.
9. **Substructural drop elaboration** — insert `drop` before returns for
   Init-at-return values whose types are Drop.

Post-elaboration checks:

10. **Init state (re-run)** — surface obligation errors at
    NLL-inserted `unborrow` sites.
11. **Substructural leak check** — strict "no Init at return."
12. **Lifetime loan check** — every access respects the active loan set.

Codegen (`src/codegen/`) emits textual LLVM IR from the elaborated MIR.
It's a separate stage that assumes the MIR is well-checked.

## Intrinsics

Silica-MIR has no built-in arithmetic or comparison syntax. Common
operations are ordinary `call` statements to functions whose names use
the reserved `$` prefix — see `src/intrinsics.rs`. Codegen intercepts
`call $name(...)` and emits the corresponding LLVM instruction sequence
inline; the intrinsic symbol never appears in the emitted `.ll`.

Adding an intrinsic that fits an existing shape is a one-file change
(one row in `intrinsics::all()`). Adding an LLVM-intrinsic-backed
operation (e.g. `@llvm.ctpop.i64`) is the same one-file change plus a
`llvm_declares` entry that codegen auto-includes in the module preamble.

Currently provided:
- Integer arithmetic: `$i64_add/sub/mul/neg`, `$u64_add/sub/mul`.
- Integer comparisons (result `bool`): `$i64_eq/ne/lt/le/gt/ge`,
  `$u64_eq/ne/lt/le/gt/ge` (signed and unsigned predicates
  respectively).
- Float arithmetic: `$f64_add`, `$f64_mul`.
- LLVM-intrinsic-backed: `$i64_popcount` (`@llvm.ctpop.i64`).

Everything else (bitwise ops, shifts, div/rem, per-width variants,
casts, saturating arithmetic, LLVM intrinsics like `ctlz`/`sqrt`) is a
row-addition away.

## Runtime

Extern functions declared in Silica lower to LLVM `declare` lines that
resolve against the platform's default libc at link time — no per-symbol
machinery, no C shim. A `write(2)` or `abort()` extern is a one-line
`extern fn` in Silica and works end-to-end.

C return values integrate through Silica's `&out $return` convention:
an extern `fn foo(a: T) -> R` is spelled as `extern fn foo(a: T, $return: &out R)`
in MIR. Codegen at the extern call site does the C-ABI translation —
issue the C call with the non-return args, store the LLVM-level return
into `*$return`. Today the codegen path is still void-only in practice
(non-void C returns get dropped); wiring up `$return`-carrying externs
is a codegen change, not a design change.

# Exploration map
This may be out of date but the directory structure is roughly as follows. 
```
src/
├── lib.rs                  # Compiler pipeline entry
├── main.rs                 # Binary entrypoint (CLI arg parsing, diagnostic rendering)
├── diagnostics.rs          # Spanned warning/error collector
├── hll/                    # High-Level Language Frontend
│   ├── ast.rs              # Surface syntax definition
│   ├── parser.rs           # HLL Tree-Sitter FFI wrapper
│   ├── type_check.rs       # HM-style type inference
│   ├── mut_check.rs        # Mutability enforcement
│   └── lowering.rs         # Lowers HLL AST to MIR CFG & sret convention
└── mir/                    # Medium Intermediate Representation
    ├── ast.rs              # MIR nodes (Places, Operands, Statements, Types)
    ├── parser.rs           # MIR Tree-Sitter parser
    ├── intrinsics.rs       # Built-in $i64_* ops and LLVM declarations
    ├── init_state/         # Initialization and reference obligations
    ├── lifetime/           # Lifetime loan checker & NLL elaborator
    ├── substructural/      # Drop elaborator & return leak checker
    └── codegen/            # Textual LLVM IR generation
```
Key files
- `main.rs` for how all the compiler passes are wired up.
- `src/hll/lowering.rs` for examples of HLL syntax and how it lowers to MIR. 
- `src/mir/init_state/mod.rs` for the substructural references model.

# Testing discipline

Compiler testing lives on a spectrum from "here's a program, here's what
should happen" (which most compiler bugs are actually about) to "does
this dataflow join commute" (which most compiler bugs are not). The
project skews toward the second today; the target is the first.

## Test tiers

1. **Fixture tests — the primary surface.** For anything that's "program
   in, artifact out." Each test is an input file paired with an
   expected-output sibling. Runner: `tests/fixtures.rs`.

   Layout:
   - `tests/{init_state,lifetime,substructural,type_check,layout,
     variant_flow,block_reachability}/{topic}/` — pass-oriented.
   - `tests/{array,string,raw_ptr,programs,error_display,intrinsic,
     main_wrapper}/` — cross-cutting features.
   - `tests/codegen/` — full pipeline + codegen → LLVM.
   - `tests/codegen-raw/` — parse + codegen (no checks) → LLVM. For
     hand-crafted programs that exercise a specific lowering but
     wouldn't pass substructural or leak checks.

   Stage detection: within a pass/feature dir the runner infers stage
   from which `.expected` sibling exists:
   - `foo.sim` + `foo.sim.expected` → clean run, compare pretty-
     printed elaborated MIR.
   - `foo.sim` + `foo.err.expected` → run produced diagnostics,
     compare rendered output (with source-snippet caret).
   - Under codegen dirs, `foo.ll.expected` compares LLVM IR.

   Expected-file extensions match the output language so editors keep
   syntax highlighting. `UPDATE_EXPECT=1 cargo test --test fixtures`
   rewrites every expected file; the runner detects stage flips
   (ok↔error) and cleans up the stale extension.

   `EXTRACT_FIXTURES=1 cargo test` — extraction mode: every test that
   goes through `test_util::run`/`run_structured` (or
   `codegen::test_util::ll_of`) writes its source string to a fixture
   file as a side effect. Used to bulk-migrate unit tests; useful in
   perpetuity when converting a new inline test to a fixture.

2. **Pass-internal unit tests — narrow.** For pass private APIs whose
   behavior isn't observable end-to-end, or invariants a fixture can't
   check. Examples: NLL snapshot tests in `nll_tests.rs` that pin the
   exact pretty-printed form after NLL only (without drop-elab);
   `check_return_leaks` invoked directly on a non-elaborated program
   (the fixture runner would insert drops and hide the intended
   failure).

3. **Utility unit tests — inline.** For small helpers with real
   invariants and no natural fixture expression:
   `dataflow` join/fixed-point/direction semantics, `cfg_edit` split-edge
   idempotence, `Markers::from_iter` canonicalization,
   `is_type_uninhabited` cycle handling, parser tree-walking
   primitives. `#[cfg(test)] mod tests` inline is fine here — the
   tests belong next to the API they exercise.

## When separate file vs inline

Not file size — **test count and kind**:
- **Sibling `*_tests.rs`**: >10 tests, or tests group naturally by
  topic (e.g. `init_state/{cfg_shape,projections,overwrite,partial_init}_tests.rs`).
- **Inline `#[cfg(test)] mod tests`**: <5 tests exercising one narrow
  API, module <500 lines.
- **`tests/` fixture dir**: anything "program in, artifact out." Never inline.

## Fixture granularity

Prefer fewer, denser fixtures per concept over many one-shot files.
For a language rule that spans a matrix of interactions (e.g. ref
kinds × container types, or generic bounds × decl kinds), aim for:

- **one success fixture** with a fn per non-trivial cell, and
- **one failure fixture** with a fn per failure mode,

both living in the same dir. Each fn's header comment states which
cell it covers. A reader skimming either file gets the full spec of
the concept in one place; a regression narrows to a single line in
one expected file.

Small, single-purpose fixtures fragment the spec across a dozen
filenames and hide the matrix. Consolidate opportunistically —
whenever you touch a topic, sweep the sibling fixtures for
subsumed cases and delete them.

## HLL over MIR when both work

When a test can be written in either surface, prefer `.si` (HLL): the
lowering path plus the checker path plus codegen is the more
end-to-end story, and any regression in either layer surfaces from
the same fixture. Reach for `.sim` (MIR) only when the checker
behavior under test can't be produced from HLL — hand-crafted CFG
shapes, specific dataflow join scenarios, or MIR features the HLL
doesn't lower to yet.

## Anti-patterns to avoid

- **Per-pass duplication of the same program.** If init_state and
  lifetime both hand-craft the same `&mut` conflict, one fixture test
  against the whole pipeline replaces both.
- **Substring-matching emitted artifacts.** `assert_contains(&ll,
  "= add i64")` in codegen tests should be a fixture whose
  `.expected.ll` is asserted exactly (with `UPDATE=1` to regenerate).
- **Success-only test suites.** Every diagnostic code should have a
  fixture pinning its rendered output. This is what forces
  diagnostic quality.
- **Testing at the wrong tier.** Reaching into a pass's private state
  to test something a fixture test would catch is a smell.

## Adding a new feature

Order of operations:
1. Add a fixture for the golden path. Watch it fail.
2. Add a fixture per error case, one per new `DiagCode` variant.
3. Only add unit tests if there's an invariant the fixture can't observe.

# Punch list

## Language features
- **HLL binary operators** `+ - * /` (currently intrinsic calls only).
  Prerequisite for real HLL ergonomics and for HLL versions of the
  existing MIR fixture programs.
- **HLL block-like expressions need `;` as statements.** `if E { ... }` (and `loop`, `match`) require a trailing `;` when used as a statement; Rust's block-like-expression rule would remove that noise.
- **HLL `extern fn` declarations.** No FFI is expressible in `.si` today — blocks HLL siblings of `tests/programs/hello_world_via_write.sim` and `heap_linked_list_of_i64.sim`. Also opens up heap allocation as a byproduct (malloc returns a raw pointer).
- **HLL `as` casts between reference / raw-pointer types.** No syntax today to reinterpret between `&T` / `&mut T` / `*T` (or between `*T` / `*U`); raw pointers stay non-null by construction — you get them from `&raw place` or from an extern.
- **Generics** in the MIR — grammar/AST/parser/print, scope-aware
  substructural composition, decl-side marker check, and
  use-site bound + arity check are all in. Remaining:
  monomorphization pass ahead of codegen (today codegen and
  layout panic on `Type::Param` and non-empty `Custom` args).
  Conditional marker declarations (`Foo<T>: Copy where T: Copy`)
  are deferred behind the current unconditional-bounds form; the
  inline form on the decl and a separate `impl`-style form will
  coexist.
- **HLL generics** — grammar, AST, parser, HLL type-check (HM +
  substitution + validate_type for decl-side arity/bounds/scope +
  generic-fn call inference), MIR `RValue::EnumConstr` and
  `ConstVal::FnName` with type args, and end-to-end lowering are
  all in. Remaining gaps:
  - **Explicit generic-fn call syntax `foo<i64>(...)`.** Inference
    works for fully-inferable calls; explicit type args need HLL
    grammar for `call_expr` + parser + type_check to accept them
    against the freshened signature.
  - **Return-type annotation span points at the fn keyword.** HLL
    `FnDecl` doesn't carry a separate span for `ret_ty`, so any
    validation error on the return type is reported at the fn
    itself. Add a span field alongside `ret_ty` to fix.
  - **Cascading errors from a poisoned type.** After a decl-side
    validation error, downstream unification produces follow-on
    diagnostics that repeat the root cause. A `Type::Error` sentinel
    that unifies with anything would silence the tail.
  - Conditional marker bounds (`Foo<T>: Copy where T: Copy`) are
    still deferred behind the unconditional-bounds form.
- **Shadowed variables in HLL lowering.** Consider `defer` interaction:
  ```
  let x = 1;
  { defer { x = 3 }  // acts on outer x?
    let x = 2;
  }
  ```
- **Reachable/flow analysis for bools.** Or reify `bool` as an enum
  and let variant_flow handle it?
- **No-alias raw pointer variant** (`*noalias T`) alongside the
  aliasing `*T`. Enables LLVM `noalias` on parameters where the
  checker can prove exclusivity.
- **HLL tuples, anonymous enums** (`(left: T | right: U)`?), and
  a Rust-shaped enum syntax (currently only newtype-with-different-
  syntax).
- **HLL uninitialized `let` bindings** (`let p: P;` with no
  initializer). Today every `let` requires an initializer, so
  field-by-field aggregate init and Partial-with-NeverInit-fields
  aren't spellable at the surface. Blocks the full HLL sibling of
  `tests/init_state/partial_init/partial_init_use.sim` — the
  current `hll_partial_init_completes.si` only covers the
  move-out-then-partial subset. Also blocks the HLL sibling of
  `tests/init_state/borrow_precondition/{borrow_precondition_met,
  borrow_precondition_violated}.sim` — the `&out` / `&uninit`
  matrix cells all require declaring an uninit-state place.
  Also blocks the HLL siblings of
  `tests/substructural/check/{class_check_ok,class_check_violations,
  return_leak_ok,return_leak_violations}.sim` — every fn declares
  an uninit destination local (for the `= copy/move` rvalue) or an
  uninit aggregate for field-by-field init, neither of which is
  spellable today.
  Separately: `tests/init_state/cfg_shape/{init_across_cfg_shapes,
  init_across_cfg_shapes_violations,borrow_across_cfg_shapes,
  borrow_across_cfg_shapes_violations}.sim` have no HLL siblings
  for a different reason — the HLL has no surface for `abort` /
  `unreachable` terminators, hand-crafted CFG shape (custom
  block labels, irreducible flow, join topology), or downcast-
  projection borrows. Every fn in those files exercises a CFG
  shape the HLL lowering doesn't produce.

## Elaboration + drop
- **HLL `break` inside a loop skips drops of block-local unit temps.** `loop { if c { break; }; ... }` fires `SUB-ReturnValueLeak` on the loop body's `_temp: unit` because drop-elab doesn't insert drops on the break edge.
- **Extend downcast-target reassignment to non-operand rvalues.**
  Today `o as V = <operand>` elaborates to `drop (o as V); o =
  EnumName::V(<operand>)`, but only when the rvalue is an Operand
  (Copy/Move/Const). For `o as V = &mut foo` or `o as V = [e0, e1]`
  the payload would need to be hoisted into a fresh temp first,
  which requires allocating a mid-elaboration local. HLL callers
  can spell the pattern manually today.
- **Drop insertion order in return blocks.** Belongs to the HLL
  (scope-nesting determines LIFO). If the frontend emits its own
  drops per scope-exit, the drop elaborator becomes reference-only.
- **Move loan-conflict dedup into elaboration.** `lifetime/mod.rs`
  currently calls `d.retain_errors` mid-check to suppress duplicate
  conflicts caused by drop-elaboration expanding `target = <rvalue>`
  into `drop target; target = <rvalue>`. Mutating diagnostics during
  checking is fragile — the fix belongs in drop-elaboration (emit a
  compound statement or synthesize a shared span).

## FFI
- **Function pointers to externs.** `Type::Fn` erases the sret-vs-
  C-ABI distinction, so a `fn(T) -> R`-typed value called through
  can't tell which ABI to use. Either ban taking pointers to externs
  or emit a Silica-shape wrapper. Blocked on first-class function-
  pointer values first.

## Diagnostics
- **Rustc-style interleaved multi-span rendering.** Primary + labeled
  secondaries merged into one continuous source block. Today each
  secondary renders as its own `= note:` snippet.
- **Cross-block borrow-origin spans.** `Analysis::transfer_stmt` in
  `mir/dataflow.rs` doesn't thread `Span`, so cross-block loans
  lose their origin and the LoanConflict secondary snippet is
  suppressed (see comment in `mir/lifetime/mod.rs`).
- **Info-severity diagnostics.** Fourth bucket alongside error /
  warning / internal_error, rendered with a `note:` prefix. First
  use case: flag redundant markers on a decl — `struct X: Copy +
  Drop + Move { ... }` gets an info note that `Move` is implied.
- **HLL parser CST→AST layer short-circuits at the first malformed
  node — should it skip the broken decl and continue?**
- **HLL lowering returns `Result<_, Diagnostic>` — should internal-
  error lowering failures accumulate the same way user errors do?**

## Testing gaps
- **Post-elab init-state re-run** has no dedicated fixture. Add one
  per obligation kind that would silently pass without the re-run.
- **Codegen fixtures don't validate the emitted LLVM.** Add a
  fixture that pipes output through `llvm-as` (skip when absent
  from `PATH`) to catch malformed IR at emit time.
- **HLL loop with ref obligations across iterations.** New coverage
  needed: no fixture yet exercises a `&out`/`&drop` obligation
  carried across loop iterations from the HLL surface.

# Longer term
- Standard library (needs generics + modules + multi-file support).
  Effects: `Fail` for exceptional control flow, `Iter` for for-loops,
  `Async` for executors.
- Round-trip fixture test (`pretty_print → parse → pretty_print`)
  as an anti-drift check between grammar and codebase.
- Tighten MIR struct/enum decl separators from whitespace-or-comma
  to comma-required-optional-trailing (match HLL).
- Coroutines. Prerequisites: generics, lifetime arguments,
  HLL `defer`, HLL binary operators.
- Lambdas.
- MIR traits.
- Silica C FFI and calling conventions: Define C linkage declarations (`extern "C" fn`) and emit standard ABI parameter attributes in LLVM.
- Translation units and multi-file compilation: Support modular compilation, imports, symbol visibility, and linking of separate Silica source files.
- Forward-declared data structures: Support opaque/external struct declarations to safely pass un-sized external resources across FFI boundaries.