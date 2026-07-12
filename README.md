# Silica-MIR
This document defines the Silica middle level intermediate representation (MIR).

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
Values in Silica are linear. Relaxations are provided by the `Drop` and `Copy`
traits, which tell the compiler that the type may be used fewer than 1 and
greater than 1 times respectively. Scalar types are both `Drop` and `Copy` so
they can be used freely.

Substructural class comes from the declaration markers:

| markers      | class        | may use twice | may be forgotten |
|--------------|--------------|---------------|------------------|
| (none)       | linear       | no            | no               |
| `Drop`       | affine       | no            | yes              |
| `Copy`       | relevant     | yes           | no               |
| `Copy Drop`  | unrestricted | yes           | yes              |

#### Initialization State tracking
Like Rust, Silica has const references, but unlike Rust, it has four kinds of
mutable reference. Each kind tracks the referent's current initialization state
and their desired initialization state at the end of the reference lifetime.

| kind    | current | end |
|---------|---------|-----|
| &mut    | yes     | yes |
| &out    | no      | yes |
| &drop   | yes     | no  |
| &uninit | no      | no  |

The shared kind `&T` is `Copy Drop` (unrestricted) — aliasable and freely
forgettable, same as Rust. The mutable kinds above are all not `Copy` to avoid
data races. `&out` and `&drop` are linear types (neither `Drop` nor `Copy`) as
they represent unfulfilled obligations to initialize or deinitialize the
referent. `&mut` and `&uninit` are affine types (`Drop` not `Copy`).

## Immovable Types
The `Move` trait tells the compiler a type is movable. Without it, it cannot be
passed by move. All scalar types are movable. If a type is `Copy` and `Drop`,
the compiler auto-derives a `Move` impl for it (see the Substructural traits
section below), unless the user has provided their own `Move` impl.

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

```
trait Copy {
  fn copy(&self, dst: &out Self);
}
trait Drop {
  fn drop(&drop self);
}
trait Move {
  fn move(&drop self, dst: &out Self);
}
// Auto-derived by the compiler for any `Copy + Drop` type unless the
// user provides their own `Move` impl. Not a Rust-style blanket impl —
// user impls take precedence, so there's no coherence conflict.
impl<T: Copy + Drop> Move for T {
  fn move(src: &drop Self, dst: &out Self) {
    Copy::copy(&*src, dst);
    Drop::drop(src);
  }
} 
```
Note that unlike Rust, `Copy` may be user defined. The same auto-derivation
rule applies: `Copy` is derived for types whose fields are all `Copy`, and
users may override.


## Effectful Copy/Move/Drop
These are vocabulary traits, for use in the standard library, but not inserted
by the compiler.
```
trait Clone {
  effects E;
  co clone(&self, dst: &out Self) -> () ! E;
}
trait Destroy {
  effects E;
  co destroy(&drop self) -> () ! E;
}
trait Transfer {
  effects E;
  co transfer(&drop self, dst: &out Self) -> () ! E;
}
```

# Silica's Compiler Plan
1. Lower from Silica to this MIR. Typecheck the source program and convert
control flow into a CFG.
2. Run analysis pass on this MIR to infer lifetimes and insert explicit
`unborrows` and `drop`s. This is the "elaborated MIR". Once
elaborated, programs should be fast to check without inference.
1. Run optimization passes on the elaborated MIR. After optimizations, we
optionally recheck the programs for correctness.

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
    | fnName                      # a bare identifier resolves to a function's address

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

function =
    | extern fn name ( var: type, ... ) ;
    | fn name ( var: type, ... ) { (var: type ;)* basic_block* }

struct_decl =
    struct [Copy? Drop? Move?] identifier { (field: type)* }

enum_decl =
    enum [Copy? Drop? Move?] identifier { (Variant: type)* }

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
- **`switchEnum` takes a place, not an operand.** It performs a *discriminant read* — a shared-read access for conflict purposes, consuming nothing. It must be a place because each out-edge refines the type of *that specific place*, which is what justifies the downcast projection in the target block. Switching on a copied temporary would sever the connection between the discriminant tested and the place downcast. (`branch` stays operand-based: `boolean` is `Copy Drop` and no refinement occurs.)
- **`abort` / `unreachable`** are terminators with no successors — runtime escape hatches. They **waive linear obligations** for code that only reaches them: elaboration passes (drop, NLL) don't insert cleanup on paths that never reach `return`, because the program dies before the caller could observe. Mixed CFGs are handled precisely — if a branch has one arm reaching `return` and one reaching `abort`, obligations are still checked on the return arm.
- **Lifetimes are inferred (NLL-style).** No lifetime annotations anywhere.
Regions are internal to the checker, derived from reference liveness.
- **Return values are modeled with `&out` parameters.** Functions have no return
type; `call` is a statement, not an rvalue. This is sret/RVO. Full Silica
has return types but lowers to this to simplify the MIR.
- **Raw pointers (`*T`, created via `&raw place`) are unsafe.** Creating a
  raw pointer does NOT create a loan; deref does not check aliasing,
  init state, or lifetime. The pointer value itself is `Copy Drop Move`.
  Use for FFI, unchecked buffer access, and pointer arithmetic
  (once we add it).
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
    | struct identifiers
    | enum identifiers
    | fn(type, ...)                              # no result type; results via &out params
    | &T | &mut T | &out T | &drop T | &uninit T # safe references (loan-tracked)
    | *T                                         # raw pointer (unsafe, aliasing)
    | [T; N]                                     # fixed-size array
```
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

## Compiler Structure
Where possible the compiler splits subsystems into independent passes.
`src/dataflow.rs` contains common forwards/backwards CFG traversal utilities
that are shared across multiple passes. The compiler splits elaboration and
checker passes. Elaboration passes add statements, such as `drop` and
`unborrow`, which make ownership/linearity transitions explicit. Checker passes
do not modify the instructions but verify their properties.

The authoritative pipeline is `run_all_passes` in `src/main.rs`.
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

Extern functions declared in Silica lower to LLVM `declare void @name(...)`
lines. Since the emitted `.ll` links against the platform's default libc
via `clang out.ll -o out`, a `write(2)` or `abort()` extern resolves at
link time with no per-symbol machinery — this is how string-printing
demos work end-to-end without a C shim. Extern signatures are `void`
because Silica has no return values; C-side non-void return values are
silently dropped (fine for demos, would need explicit `&out` plumbing
for production correctness).



# Punch list
- HLL
- Special $return MIR variable that maps to the return place in the HLL and
in LLVM.
- reachable/flow analysis for bools too. Or should bool be an enum?
- Design MIR coroutines and effect decls.
- Extend downcast-target reassignment drop-elab to non-operand
  rvalues. Today `o as V = <operand>` rewrites to
  `drop (o as V); o = EnumName::V(<operand>)` — but only when the
  rvalue is an operand (Copy/Move/Const), because `EnumConstr`
  takes an Operand. For `o as V = &mut foo` or `o as V = [e0, e1]`
  we'd need to hoist the payload into a fresh temp first, which
  requires allocating a mid-elaboration local. Frontend can spell
  the pattern manually today.
- No-alias raw pointer variant (`*noalias T`) — currently we only have
  the aliasing `*T`. Would enable `noalias` attributes on parameters
  where the checker can prove exclusivity.

## Elaboration gaps
- Drop insertion *order* within a return block is a HLL responsibility
  (scope-nesting determines LIFO). At the MIR level drops are already
  explicit statements; the elaborator only inserts what would otherwise
  leak. If the frontend emits its own drops per scope-exit rules, the
  drop elaborator becomes reference/debug-only rather than authoritative.

## Diagnostics
- Type names print as Rust `{:?}` debug form (`Int(I64)` instead
  of `i64`). Route diagnostic-emitting sites through
  `pretty_print::write_type`.
- Errors give `at L:C:` but no source snippet with a caret.
  Rustc-style rendering (source line + caret span + message)
  would help enormously. Prerequisite: widen `Span` from
  `{ line, col }` to byte offsets so the renderer can slice
  the source line and place the caret precisely.
- No tags. Prefixing tests with `[init_state]` / `[lifetime]` / `[correct]`
  etc. would speed grep-based navigation.
- Golden IR snapshot failures print two blobs; a line-by-line
  diff would make regressions instant to read.
- Common-mistake hints. When `cannot create &out of X` fires and
  `X` is init, "hint: consider `drop X;` before rebinding" would
  save first-time users a lot of time.

# Longer term
- Split `grammar.js` into `common/` (types, identifiers, literals,
  struct/enum decls, markers) plus `hll/` and `mir/` grammars that
  consume the common rules via JS `require`. Retire the hand-rolled
  HLL parser once the tree-sitter HLL grammar reaches parity.
- Round-trip corpus test (`pretty_print → parse → pretty_print`)
  as an anti-drift check between grammar and codebase.
- Tighten MIR struct/enum decl separators from
  whitespace-or-comma (current: either works) to comma-required-
  optional-trailing to match HLL. Currently permissive to keep
  existing MIR programs working.
- Allow an optional trailing `;` after MIR terminators
  (`return;`, `goto foo;`, ...) — currently rejected, which is
  irritating when writing MIR by hand.
- Lambdas
- Coroutines
- MIR polymorphic types
- MIR traits?
- Silica HLL lowering