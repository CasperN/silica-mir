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

## Substructural types
Values in Silica are linear. Relaxations are provided by the
`Drop` and `Copy` traits, which tell the compiler that the type can be used
0 or 1 times and 1 or more times respectively. Scalar types are both `Drop` and
`Copy` so they can be used freely.

Substructural class comes from the declaration markers:

| markers      | class        | may use twice | may be forgotten |
|--------------|--------------|---------------|------------------|
| (none)       | linear       | no            | no               |
| `Drop`       | affine       | no            | yes              |
| `Copy`       | relevant     | yes           | no               |
| `Copy Drop`  | unrestricted | yes           | yes              |

#### Initialization State tracking
Silica has four kinds of mutable reference. Each kind tracks the referent's
current initialization state and the desired initialization state at the end of
the reference's lifetime.

| kind    | start | end |
|---------|-------|-----|
| &mut    | yes   | yes |
| &out    | no    | yes |
| &drop   | yes   | no  |
| &uninit | no    | no  |

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
    | unborrow place
        # Mark the place as no longer borrowed. Inserted by the NLL pass.
        # Legal iff the loan on x has a fully dead lineage -- the reference and
        # every continuation derived from it consumed/forgotten.
    | place, place = deref_move place
        # dst, src' = deref_move src
        # If src: &mut T, src': &out T
        # If src: &drop T, src': &uninit T
    | place = deref_init(place, operand)
        # p' = deref_init p operand
        # if p: &out T, p': &mut T
        # if p: &uninit T, p': &drop T

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

# Analysis pass
The analysis pass is **insertion-only**: it may add locals, statements,
and blocks (edge splitting); it never rewrites, reorders, or renames
existing code, and inserted names are used only by inserted statements.

It inserts: `unborrow`s at inferred loan ends (liveness-based), copies, and
drop-call sequences for dead values (including per-edge
join resolution). A fully explicit program passes the checker with
nothing inserted; the pass is idempotent and validated by re-running
the checker on its output.

## Loans and lineages

A borrow freezes its base and starts a **lineage**: the chain of names
through transitions. A lineage — and its loan — closes at exactly one
of two syntactic points:

- **`unborrow r`** — consumes `r`; requires cur == post. Only applies to
  exclusive references; `&T` is `Copy Drop` and needs no closure. If the
  lineage originated at a borrow of a local base, the base thaws to the
  loan's post (`Init` for `&mut`/`&out`, `Uninit` for `&drop`/`&uninit`).
  If the lineage is a reference *parameter's*, this discharges the
  signature obligation instead (there is no local base).
- **a call consuming the reference operand** — the callee's signature
  is trusted; the base thaws to the loan's post immediately after the
  call.

`&out`/`&drop` cannot be unborrowed (cur ≠ post): they must first be
transitioned or passed to a call — that refusal is the obligation.

Borrow bases must be owned paths (no deref of an exclusive reference
in a borrowed place); reborrows are a planned extension. Assignment
destinations must likewise be owned paths — all mutation through
references goes via `deref_move`/`deref_init`.

# Checking

The checker is a forward dataflow analysis; no lifetime inference. State
per program point: the **init tree** — each move path (locals and their
projections through fields and downcasts) is `Uninit | Init |
Partial(fields) | Frozen(loan)`. Enums are atomic: moving a downcast
payload sets the whole enum `Uninit`.

- **Freezing:** while a base is `Frozen`, no reads, writes, moves, or
  borrows of it, any prefix, or any extension. Loans on disjoint fields
  coexist, mixed kinds included.
- **Joins:** predecessors must agree per move path. Disagreement is an
  error unless the path's type permits weakening (`Drop` without a
  destructor, `Copy Drop`) — the analysis pass resolves other
  disagreements by inserting drop sequences on the initialized edges
  (splitting critical edges as needed).
- **Leak check at `return`:** every move path `Uninit`, every loan
  closed, every reference-parameter lineage discharged — except
  weakening-permitted paths, which may be left `Init`. A body holding
  an untransitioned `&out`/`&drop` parameter cannot close it and fails
  here; that is the whole enforcement of signature obligations.
- **Downcast refinement:** `p as V` is legal iff `p` is `Init` and the
  point is dominated by a `switchEnum(p) → V` edge with no intervening
  kill: any write to, move from, or borrow of `p` or a prefix
  (including passing `&mut p` to a call — `&mut` does not preserve the
  variant). `switchEnum` arms must be syntactically total over the
  declaration (a declaration-level check).

