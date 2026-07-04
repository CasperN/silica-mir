# Silica-MIR

The goal of this document is to define a lower-level language than Silica that exercises the core linear types, borrowing, and initialization-state checking. It is a low-level control-flow-graph IR, not intended to be written by regular programmers.

Deliberate simplifications (revisit when lifting restrictions):
- **Calls are total.** No unwinding, no divergence, no effects. When abort-as-recoverable/unwind/effects are added, calls grow explicit continuation (and cleanup) edges. Coroutines do not change this: a coroutine is an ordinary value returned by its factory function; *running* it is outside Silica-lite.
- **No user-defined copy, move, or drop.** `copy` and `move` are bitwise primitives, and an implicit "drop" is really a **forget** — bitwise erasure, running no code. User-defined `Copy::copy`, `Move::move(old: &drop Self, new: &out Self)`, and `Drop::drop(self: &drop Self)` are expressible as *ordinary functions* in this system (the reference kinds encode their entire contract), but Silica-lite never inserts calls to them implicitly, and types with such impls would not be bitwise-movable. Full Silica's MIR elaborating implicit forgets/copies/moves into implicit *calls* is a real design step (a lowering compiler, not just a checker) — deferred, to be discussed.
- **Lifetimes are inferred (NLL-style).** No lifetime annotations anywhere. Regions are internal to the checker, derived from reference liveness.
- **Results are returned through `&out` parameters.** Functions have no return type; `call` is a statement, not an rvalue. This is sret/RVO as semantics rather than optimization, and it makes the leak check at `return` uniform. Full Silica keeps return types and lowers to this.

# Grammar

```
place =
    | var
    | place.field                 # struct field projection
    | (place as Variant).payload  # enum downcast projection (only valid in blocks
                                  #   dominated by the corresponding switchEnum edge
                                  #   on that same place)
    | *place                      # deref of a reference

const = number | true | false | fnName

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

terminator =
    | goto label
    | return
    | branch(operand) [ true: label, false: label ]
    | switchEnum(place) [ Variant: label, ... ]
    | abort
    | unreachable

basic_block = label : (statement ;)* terminator

function =
    fn name ( var: type, ... ) {
        (var: type ;)*   # locals
        basic_block*     # CFG; first block is entry
    }

struct_decl =
    struct [Copy? Drop?] identifier { (field: type)* }

enum_decl =
    enum [Copy? Drop?] identifier { (Variant: type)* }

extern_fn =
    extern fn name ( var: type, ... ) ;   # signature only, no body

declaration = struct_decl | enum_decl | function | extern_fn

program = (declaration ;)*
```

Notes:
- `move`/`copy` is explicit on every operand so the linearity check is local and syntax-directed.
- Struct construction has **no aggregate rvalue**. Structs are initialized one field at a time via `x.field = ...`; the struct as a whole is initialized exactly when all fields are.
- Enum construction *is* whole-value (`Name::Variant(operand)`): a variant's payload and discriminant must become valid atomically.
- **`switchEnum` takes a place, not an operand.** It performs a *discriminant read* — a shared-read access for conflict purposes, consuming nothing. It must be a place because each out-edge refines the type of *that specific place*, which is what justifies the downcast projection in the target block. Switching on a copied temporary would sever the connection between the discriminant tested and the place downcast. (`branch` stays operand-based: `boolean` is `Copy Drop` and no refinement occurs.)
- **`abort`** is dynamic termination: no successors, and the one point where `&out`/`&drop` obligations and the leak check are waived — the escape hatch a linear language needs for runtime invariant violations.
- **`unreachable`** is not abort and runs nothing: a block whose terminator is `unreachable` must have an **empty statement list**. It is a named hole — a label the grammar forces you to provide but that control provably never reaches (e.g., a `switchEnum` arm ruled out by prior refinement). The checker treats its state as ⊥ and must be able to *verify* unreachability; a development build may lower it to a trap.

# Types

```
type =
    | number
    | boolean
    | struct identifiers
    | enum identifiers
    | fn(type, ...)                              # no result type; results via &out params
    | &T | &mut T | &out T | &drop T | &uninit T
```

Substructural class comes from the declaration markers:

| markers      | class        | may be bitwise-copied | may be forgotten |
|--------------|--------------|-----------------------|------------------|
| (none)       | linear       | no                    | no               |
| `Drop`       | affine       | no                    | yes              |
| `Copy`       | relevant     | yes                   | no               |
| `Copy Drop`  | unrestricted | yes                   | yes              |

`Drop` here means *forgettable* (bitwise erasure), not "has a destructor" — no user code runs at this level.

`number`, `boolean`, `fn`, and `&T` are `Copy Drop`. The exclusive reference kinds are `Drop` (not copyable; the reference *value* may be forgotten — but forgetting it expires the loan, and loan expiry checks the obligation below, so "forgettable" does not mean "obligation-free").

# References

`&T` is the shared kind: pointee must be initialized, read-only, aliasable with other `&T` loans, no state change.

## The exclusive kinds are one type with two bits

An exclusive reference is a pair **(cur, post)** over {init, uninit}:

- **cur** — the pointee's current initialization state. *Flow-sensitive*: tracked by the checker, changed by operations through the reference.
- **post** — the state the pointee must be in when the loan expires. *Fixed at loan creation*; part of the static type at function boundaries.

The four surface names denote the corners; a name written in a signature or borrow rvalue specifies (cur-at-creation, post):

|                  | post = init | post = uninit |
|------------------|-------------|---------------|
| **cur = init**   | `&mut`      | `&drop`       |
| **cur = uninit** | `&out`      | `&uninit`     |

Operations through an exclusive reference `r` move it **vertically**; post never changes:

- `*r = v` — write into uninit pointee: `&out → &mut`, `&uninit → &drop`
- `move *r` — consume pointee: `&mut → &out`, `&drop → &uninit`
- reads (`copy *r`, shared reborrow) require the read part of the pointee to be init; no transition

**Expiry rule:** a loan may expire only where `cur == post` (field-granularly: the pointee's init tree fully matches post). So `&out` must be fully initialized, `&drop` fully deinitialized, at every point the loan can expire. Deinitializing through `&mut` is *legal* — it transitions to `&out` state, and the obligation forces re-initialization before expiry (the take-and-put-back pattern: `swap`, `replace`, in-place transforms, with no trusted primitive needed).

**Call rule:** passing a reference to a callee parameter declared `(pre, post')` requires `cur == pre`; afterward the caller's `cur := post'`. The caller's own post is unaffected — kinds compose by sequencing, no subtyping lattice. (E.g., pass your `&mut` to a callee taking `&drop`: you get back `cur = uninit`, and your `post = init` obligation forces a refill.)

**Reborrow propagation:** reborrowing takes the parent to the child's creation-cur and suspends the parent; when the child loan expires, the parent's `cur` becomes the child's post. E.g. `r2 = &drop *r1` with `r1` in `&mut` state: while `r2` is live, `*r1` is inaccessible; when `r2` expires (obligation: pointee uninit), `r1` is in `&out` state. The checker tracks pointee state through reference chains; this is tractable precisely because post is static.

**`&uninit`** is an opaque storage token (uninit → uninit, no pointee access of its own). Its use pattern is transition or reborrow: initialize through it (becoming/lending `&drop` state) and consume again before expiry — threading uninitialized storage through calls, placement-style.

# Checker

The checker is a forward dataflow analysis over the CFG. The abstract state at each program point is:

```
State = (Init, Loans)
```

## Init: the initialization tree

`Init` maps each **move path** to `Uninit | Init | Partial(children)`.

Move paths are locals and their transitive projections through struct fields, enum downcasts, and — new with the state machine — **derefs of exclusive references** (pointee state must be tracked to check transitions and expiry). Shared `&T` derefs are not move paths (always init, read-only). `Partial` appears only for structs; enums are atomic (`Init` or `Uninit` as a whole — moving a payload out via downcast sets the whole enum `Uninit`).

## Loans

A loan is `(place, post, region)` created by a borrow rvalue (shared loans carry no post). Regions are computed NLL-style: the set of program points where the created reference, or anything derived from it, is live. A loan is **in force** throughout its region and **expires** at the region's boundary points.

Conflict rules while a loan on place `p` is in force (applies to `p`, any prefix of `p`, and any extension of `p`):

| loan kind | permitted other access to p |
|-----------|------------------------------|
| shared    | reads, other shared loans    |
| exclusive | nothing — no reads, writes, moves, or other loans, except *through* the reference (or a reborrow of it) |

Moving or reassigning the **base** of any live loan is an error (no kill rule; it is simply a conflict). Loans on *disjoint* fields of the same struct do not conflict, including mixed kinds: `&out x.a` and `&drop x.b` may coexist.

## Transfer functions

Statements (state before → after):

```
p = operand
    copy q : requires Init(q), q's type Copy, no exclusive loan on q → Init(p) := Init
    move q : requires Init(q), no live loan on q                     → Init(q) := Uninit; Init(p) := Init
    const  :                                                         → Init(p) := Init
  In all cases: requires Init-state(p) = Uninit, or p's type is Drop-classed
  and an implicit forget is inserted first. Writing p.field on a Partial or
  Uninit base is the field-granular init path. If p is *r or a projection
  under one, this is a write through r: apply the state-machine transition
  (requires r exclusive; the written part of the pointee must be Uninit).

call f(a1, ..., an)
    each ai is an operand or reference (rules above / call rule). For each
    reference argument, require cur == callee pre; set cur := callee post
    at whichever point that argument's loan expires (immediately after the
    call in the common case of a borrow created at the call site).

p = &q / &mut q / &out q / &drop q / &uninit q
    requires Init-state(q) matches the kind's creation-cur; creates loan;
    if q is behind a parent exclusive reference, the parent is suspended
    until this loan expires (reborrow propagation) → Init(p) := Init

p = Name::Variant(a)
    operand rule for a → Init(p) := Init
```

Terminators:

```
branch(op)        : operand rules (boolean is Copy Drop)
switchEnum(place) : discriminant read of place (shared-read access; requires
                    Init(place); consumes nothing); each edge enables the
                    downcast projection for its variant on that place
goto              : no state change
return            : leak check below
abort             : no successors; all obligations and the leak check waived
unreachable       : block must be empty; state is ⊥; unreachability must be
                    verifiable from dominance/refinement
```

**Loan expiry** (at any boundary of a region): require the pointee's init tree to fully match the loan's post; then, if the loaned place is behind a parent exclusive reference, set the parent's `cur` to that post.

## Implicit forgets

Forgets are **inferred, not written**, and run no code (bitwise erasure). The checker inserts a forget of place `p` when:
1. `p`'s type is Drop-classed, and
2. `p` is `Init` but dead on all paths, or about to be overwritten, or a CFG join requires it.

Forgetting sets the path to `Uninit` and is legal only with no live loan on `p`. For linear/relevant types, the same situations are **errors**: the value must be explicitly consumed on every path.

## Join rule

At a block with multiple predecessors, for each move path:
- All predecessors agree → that state.
- Disagreement, Drop-classed type → insert an implicit forget on each incoming edge where the path is `Init`; joined state is `Uninit`. (Static per-edge insertion; no dynamic drop flags exist in Silica-lite.)
- Disagreement, linear/relevant type → error.

Loan sets join by union; regions are computed globally, so this falls out of the region computation.

## Leak check (return)

At `return`, **every** local and field-path must be `Uninit` — no exceptions, since there is no return place. Drop-classed paths receive implicit forgets; any linear path still `Init` is an error. Reference parameters are checked by the expiry rule: each parameter loan's region ends at `return`, so the pointee must match its declared post (`&out` params fully init, `&drop` params fully uninit, `&mut` params restored to init).

## Signature checking

A function is checked once against its declared signature (polymorphism-ready: nothing depends on concrete instantiation beyond substructural class and field structure):
- By-value parameters start `Init`; reference parameters start with a loan in force for the whole body, pointee assumed in the kind's creation-cur.
- Obligations on reference **parameters** are discharged at `return` via the expiry rule. This is exactly what lets callers apply the call rule at call sites without seeing the callee body.
- **Extern functions** are signatures with no body. Callers treat them identically to defined functions (the call rule needs only the signature); the checker *trusts* that the missing body would discharge its obligations. Externs are the sole source of primitive computation (there are no operators — `add` is an extern with an `&out` result) and the designated trusted-code boundary: capabilities inexpressible in lite (e.g., allocation returning `&uninit` storage) enter as externs with honest signatures.
