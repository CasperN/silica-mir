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
    | var
    | place.field                 # struct field projection
    | place as Variant            # enum downcast projection
    | *place                      # deref of a reference

const = number | true | false | fnName | unit

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
    | Name::Variant(operand)      # enum construction (whole-value)

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
- **`switchEnum` takes a place, not an operand.** It performs a *discriminant read* — a shared-read access for conflict purposes, consuming nothing. It must be a place because each out-edge refines the type of *that specific place*, which is what justifies the downcast projection in the target block. Switching on a copied temporary would sever the connection between the discriminant tested and the place downcast. (`branch` stays operand-based: `boolean` is `Copy Drop` and no refinement occurs.)
- **`abort` / `unreachable`** are terminators with no successors — runtime escape hatches. They **waive linear obligations** for code that only reaches them: elaboration passes (drop, NLL) don't insert cleanup on paths that never reach `return`, because the program dies before the caller could observe. Mixed CFGs are handled precisely — if a branch has one arm reaching `return` and one reaching `abort`, obligations are still checked on the return arm.
- **Lifetimes are inferred (NLL-style).** No lifetime annotations anywhere.
Regions are internal to the checker, derived from reference liveness.
- **Return values are modeled with `&out` parameters.** Functions have no return
type; `call` is a statement, not an rvalue. This is sret/RVO. Full Silica
has return types but lowers to this to simplify the MIR.

## Types

```
type =
    | unit
    | number
    | boolean
    | never                                      # uninhabited (⊥); vacuously Copy Drop Move
    | struct identifiers
    | enum identifiers
    | fn(type, ...)                              # no result type; results via &out params
    | &T | &mut T | &out T | &drop T | &uninit T
```
Note: by-value recursion is rejected as it would require infinite sizes.

## Compiler Structure
Where possible the compiler splits subsytems into independent passes.
`src/dataflow.rs` contains common forwards/backwards CFG traversal utilities
that are shared across multiple passes. The compiler splits elaboration and
checker passes. Elaboration passes add statements, such as `drop` and
`unborrow`, which make ownership/linearity transitions explicit. Checker passes
do not modify the instructions but verify their properties.

The essential elaboration and check passes are:
1. Simple type checking
2. Flow sensitive analysis to verify enums are handled safely
3. Lifetime elaboration to insert `unborrow` statements as early as possible
4. Substructural elaboration to add `drop` statements before returns.
5. Lifetime checking
6. Substructural checking.



# Punch list
- Pointers
- Strings
- FFI? Varadic externs?
- HLL
- reachable/flow analysis for booleans too. Or should boolean be an enum?
- Design MIR coroutines and effect decls.
- **Enum-payload loan transfer.** `capture_carried_refs` in `init_state`
  only transfers loans and ref-states for `Use(Move(src))` rvalues.
  `Wrap::W(move b)` (an `EnumConstr`) drops b's loans instead of
  re-keying them under `w as W`. Unsound when the payload holds a
  bound reference. Fix: extend the transfer to `EnumConstr` rvalues,
  rekeying src.* → (dst as V).* for the constructed variant.

## Elaboration gaps
- Drop insertion *order* within a return block is a HLL responsibility
  (scope-nesting determines LIFO). At the MIR level drops are already
  explicit statements; the elaborator only inserts what would otherwise
  leak. If the frontend emits its own drops per scope-exit rules, the
  drop elaborator becomes reference/debug-only rather than authoritative.

# Longer term
- Lower to LLVM
- Lambdas
- Coroutines
- MIR polymorphic types
- MIR traits?
- Silica HLL lowering