# Silica-MIR
This document defines the Silica middle level intermediate representation (MIR).

## Background on Silica
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

### Substructural types
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


### Silica's Compiler Plan
1. Lower from Silica to this MIR. Typecheck the source program and convert
control flow into a CFG.
2. Run analysis pass on this MIR to infer lifetimes and insert explicit
`unborrows`, `drop`s, and `copy`s. This is the "elaborated MIR". Once
elaborated, programs should be fast to check without inference.
3. Run optimization passes on the elaborated MIR. After optimizations, we
optionally recheck the programs for correctness.


# Grammar

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
    struct [Copy? Drop?] identifier { (field: type)* }

enum_decl =
    enum [Copy? Drop?] identifier { (Variant: type)* }

declaration = struct_decl | enum_decl | function

program = (declaration ;)*
```

Notes:
- `move`/`copy` is explicit on every operand so the linearity check is local and syntax-directed.
- Struct construction has **no aggregate rvalue**. Structs are initialized one field at a time via `x.field = ...`; the struct as a whole is initialized exactly when all fields are.
- Enum construction *is* whole-value (`Name::Variant(operand)`): a variant's payload and discriminant must become valid atomically.
- **`switchEnum` takes a place, not an operand.** It performs a *discriminant read* — a shared-read access for conflict purposes, consuming nothing. It must be a place because each out-edge refines the type of *that specific place*, which is what justifies the downcast projection in the target block. Switching on a copied temporary would sever the connection between the discriminant tested and the place downcast. (`branch` stays operand-based: `boolean` is `Copy Drop` and no refinement occurs.)
- **`abort`** is dynamic termination: no successors, and the one point where `&out`/`&drop` obligations and the leak check are waived — the escape hatch a linear language needs for runtime invariant violations.
- **Lifetimes are inferred (NLL-style).** No lifetime annotations anywhere.
Regions are internal to the checker, derived from reference liveness.
- **Return values are modeled with `&out` parameters.** Functions have no return
type; `call` is a statement, not an rvalue. This is sret/RVO. Full Silica
has return types but lowers to this to simplify the MIR.

# Types

```
type =
    | unit
    | number
    | boolean
    | struct identifiers
    | enum identifiers
    | fn(type, ...)                              # no result type; results via &out params
    | &T | &mut T | &out T | &drop T | &uninit T
```

# Compiler Structure
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
- Requre `Move` to move, `Copy + Drop` is move.
- reachable/flow analysis for booleans too. Or should boolean be an enum?
- `switchEnum(o as V)` on an inline downcast doesn't refine — the outer
  variant isn't proven before the inner switch reads its discriminant.

## Elaboration gaps
- Drop insertion order is by declaration, not initialization. LIFO by
  initialization time needs per-write sequence numbers on statements.
- If the frontend emits its own drops (per scope-exit rules), the drop
  elaborator becomes reference/debug-only rather than authoritative.


## Elaboration should not affect declarations
Currently `run_all_passes` rebuilds the `Env` after elaboration. Elaboration
passes should just mutate function bodies in place and have no effect on
declarations.

# Longer term
- Lower to LLVM
- Lambdas
- Coroutines
- MIR polymorphic types
- MIR traits?
- Silica HLL lowering