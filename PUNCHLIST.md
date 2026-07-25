# Punch list

Deferred work and known gaps. Items get added, refined, and closed as
the compiler evolves; treat entries as snapshots, not commitments.

## Copy Relaxation
- **Enforce the dynamic-place no-consumption rule at init-state.** The
  resolver already forces `take` on a dynamic-index path to `copy`, but
  hand-written MIR could still express `move a[i]` or `drop a[i]`.
  Init-state checking must reject dynamic `move`/`drop` and
  state-changing borrows while retaining the uniform-state
  read/mutation cases described in the semantics above.

## Language features
- **Standardize `&drop` vs `&deinit`.** Same reference kind
  (`RefKind::Drop`) has two surface names — MIR uses `&drop`, HLL uses
  `&deinit`. Every fixture author, diagnostic reader, and agent has
  to remember the mapping. Pick one across both surfaces (or make one
  a strict alias) and delete the other.
- **Lifetime annotations on MIR fn signatures and datastructures.** NLL infers lifetimes intra-fn, but there's no way to express "the returned `&T` is bounded by the input `&Foo`'s lifetime" or "this struct field's ref outlives the struct." Blocks safe ref-returning fns, ref-carrying types that get returned/stored, and any principled ref-cast story (`*T as &T` would conjure a reference with no lifetime bound; `&mut T as &T` is really a permission downgrade and needs a distinct MIR op).
- **HLL match on projection places.** `a[i] match { ... }` and `foo.field match { ... }` fire `VF-DowncastOnProjection` because variant flow tracks root Vars only. Users must extract to a local first (`let t = a[i]; t match { ... }`) or wrap the decode in a helper fn that takes the value by parameter. Fixable by either (a) copying/moving the projection into a fresh local during HLL lowering or (b) extending variant flow to track projections.
- **Generics in the MIR — remaining.** All checker + elab passes are in, monomorphization is in (`src/mir/mono`), and codegen emits LLVM quoted names for mono'd instantiations. Only conditional marker declarations (`Foo<T>: Copy where T: Copy`) are still deferred behind the unconditional-bounds form; the inline form on the decl and a separate `impl`-style form will coexist.
- **HLL generics gaps**
  - **Explicit generic-fn call syntax `foo<i64>(...)`.** Inference
    works for fully-inferable calls; explicit type args need HLL
    grammar for `call_expr` + parser + type_check to accept them
    against the freshened signature.
  - **Struct field, enum variant, fn param, and `let` type-annotation spans point at the whole `name: Type`.** Same fix shape as the ret_ty span already landed — add a `ty_span: Span` alongside each `ty: Type` and thread through the `validate_type` calls.
  - Conditional marker bounds (`impl<T: Copy> Copy for Foo<T> {}`).
- **Array index and array length should be `u64`.** Today `place[operand]`
  and `[T; N]` both use `i64` in the parser and checker, mirroring MIR
  integers. Sizes and offsets are inherently non-negative — matches
  `$sizeof<T>` returning `u64`. Switch `Type::Array(inner, size: u64)`
  and the index operand's expected type to `u64`. Ripples through the
  array-lit codegen (`getelementptr ..., i64 0, i64 i`) and every
  fixture that indexes an array with an `i64` literal.
- **Decide how `bool`-driven reachability is analyzed.** Today `branch(true)`/`branch(false)` don't get folded, so trivially-dead arms count as reachable. Either add a small constant-folding pass over `bool` operands, or reify `bool` as an enum so `variant_flow` handles it uniformly. Blocks tighter dead-arm warnings and short-circuit const evaluation. Decision + fixture.

## Lifetime checker gaps (semantic)
- **Bound-RHS lifetimes must be declared params.** `<'a: 'b>` requires
  `'b` in the same `<>` list; Rust auto-introduces bound-only names.
  Silica keeps this explicit — arguably fine, but worth documenting.
- **Call-site missing-bound fires wrong diag.** When a caller lacks
  the axiom a callee requires, the checker fires `LT-LifetimeEscape`
  (Free escaping into Named via the ret-out slot) rather than
  `LT-LifetimeMismatch`. Program is rejected but the code is
  misleading.
- **Invariant unification not recognized in escape check.** When
  `walk_call_regions` walks an exclusive-kind ref (e.g. `&out &'a T`
  as a callee param passed a caller `&out &'p T`), it emits both
  `(caller, inst)` and `(inst, caller)` — the inst region is
  effectively equal to the caller region. Today `check_constraints`
  treats each direction independently, so the `(Free, Named)` half
  fires `LT-LifetimeEscape` on valid forwarding calls like
  `identity(x, &out $return.*)`. Fix: precompute the set of
  bidirectional constraints (or a proper union-find on regions) and
  suppress escape when the pair is mutual — the Free is unified with
  the Named, not escaping into it.
- **Elision doesn't backfill Custom lifetime args.** Elision auto-adds
  `'sN` params to structs/enums/fns based on unannotated `&T` refs in
  their signatures, but never fills those synthesized lifetimes into
  Custom self-mentions or bare local decls. So `struct StructRefSelf
  { next: &mut StructRefSelf }` becomes `struct<'s0> StructRefSelf
  { next: &'s0 mut StructRefSelf }` — the inner mention still has
  zero lifetime args while the decl now has one param. Also blocks
  a lifetime-args arity check in `Env::validate_type`: adding one
  today rejects every bare Custom mention that relied on elision.
  Fix: two-pass elision — first collect each decl's post-elision
  param count, then backfill Custom mentions with fresh lifetimes
  (also added to the containing scope's params) — then add the
  arity checfk.
- **Call-site handling ignores fn pointers.** `Const::FnName` matches; `copy fn_ptr(args)` doesn't. Silent hole. Needs first-class fn-value lifetime tracking (`Type::Fn` doesn't carry lifetime bounds today). The variance machinery is already pre-wired for this: `Variance::Covariant` and its `combine`/`emit_variance` branches encode the standard `fn(X) -> Y` composition rule (contravariant in X, covariant in Y), but nothing constructs `Covariant` because `walk_call_regions` doesn't descend into `TypeKind::Fn`.
- **`walk_ref_paths` and `walk_regions` skip `TypeKind::Array`.** Owned `[&mut T; N]` slots aren't added to the NLL borrower set or assigned per-slot regions. Sound because loan tracking still catches conflicts and place-state materialises RefState lazily on access, but NLL won't insert `unborrow a[k]` on last-use and inter-fn lifetime constraints don't flow through array slots. Fix when arrays appear in signatures with lifetime arguments.
- **No fixture for nested-ref case (`&&i64`, `&Wrap<i64>`), shared-ref returns read multiple times, or `Wrap<'a>` in fn signatures.** Adversarial coverage gap; adversarial testing after-commit rule should catch these when the next lifetime feature lands.

## Elaboration + drop
- **`walk_diverged` skips arrays and enum Custom types.** Cross-edge
  drop planning doesn't insert per-slot / per-variant drops for
  Diverged elements — the final `check_return_leaks` still fires
  (its walk descends arrays), so sound but forces the user to
  manually drop on the initializing arm rather than relying on the
  elaborator.

## Init-state: split analysis from checking

Architecture invariant, current violation, target shape, and
prerequisite blocker are documented on `elaborate_and_check_mir`
in `src/lib.rs`, next to the code they describe.


## FFI
- **`Type::Fn` erases ABI.** A `fn(T) -> R`-typed value carries no ABI info, so calling through a fn pointer can't dispatch Silica-sret vs C-ABI. Once C-ABI externs are wired through codegen (see the extern ABI item under Language features), a fn pointer taken to an extern would need either a Silica-shape wrapper or a ban at the pointer-taking site.

## Testing gaps
- **End-to-end runtime fixtures.** `tests/programs/*` today pins elaborated MIR, but real behavior — `sum_to_n(10) → 55`, `hello_world` prints `hi!\n`, linked-list `exit=6` — is only verified manually. Automate: compile to `.ll`, link any sibling C shim, execute, pin exit code + stdout in a `.run.expected`. Needs a new fixture-runner stage + `clang` gating. Bazel migration (see Longer term) is one path to the cross-language build infra this requires.

## Longer term
- **Bazel-based build with proper cross-language infra.** Today the compiler is `cargo`, and any cross-language wiring (LLVM IR emission → `clang` link → binary → runtime → check exit) is manual. A Bazel migration would let end-to-end runtime tests, C-shim linking, and future host-language integrations (LLVM tooling, wasm, cross-compile) be first-class build actions in a hermetic graph. The immediate motivator is the End-to-end runtime fixtures item in Testing gaps.
- **HLL tuples, anonymous enums** (`(left: T | right: U)`?), and a Rust-shaped enum syntax (currently only newtype-with-different-syntax).
- **No-alias raw pointer variant** (`*noalias T`) alongside the aliasing `*T`. Enables LLVM `noalias` on parameters where the checker can prove exclusivity.
- Standard library (needs generics + modules + multi-file support).
  Effects: `Fail` for exceptional control flow, `Iter` for for-loops,
  `Async` for executors.
- `std::span<'a, T>` and `std::String`
  - Pointer arithmetic.
  - `impl AutoDestroy for String`
  - HLL lifetimes.
  - Phantom data?
- Round-trip fixture test (`pretty_print → parse → pretty_print`)
  as an anti-drift check between grammar and codebase.
- Tighten MIR struct/enum decl separators from whitespace-or-comma
  to comma-required-optional-trailing (match HLL).
- Coroutines. Prerequisites: generics, lifetime arguments, HLL `defer`.
- Lambdas.
- MIR traits.
- Silica C FFI and calling conventions: Define C linkage declarations (`extern "C" fn`) and emit standard ABI parameter attributes in LLVM.
- Translation units and multi-file compilation: Support modular compilation, imports, symbol visibility, and linking of separate Silica source files.
- Forward-declared data structures: Support opaque/external struct declarations to safely pass un-sized external resources across FFI boundaries.
