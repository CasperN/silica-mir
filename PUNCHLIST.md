# Punch list

Deferred work and known gaps. Items get added, refined, and closed as
the compiler evolves; treat entries as snapshots, not commitments.

## Language features
- **Standardize `&drop` vs `&deinit`.** Same reference kind
  (`RefKind::Drop`) has two surface names — MIR uses `&drop`, HLL uses
  `&deinit`. Every fixture author, diagnostic reader, and agent has
  to remember the mapping. Pick one across both surfaces (or make one
  a strict alias) and delete the other.
- **Lifetime annotations on MIR fn signatures and datastructures.** NLL infers lifetimes intra-fn, but there's no way to express "the returned `&T` is bounded by the input `&Foo`'s lifetime" or "this struct field's ref outlives the struct." Blocks safe ref-returning fns, ref-carrying types that get returned/stored, and any principled ref-cast story (`*T as &T` would conjure a reference with no lifetime bound; `&mut T as &T` is really a permission downgrade and needs a distinct MIR op).
- **HLL match on projection places.** `a[i] match { ... }` and `foo.field match { ... }` fire `VF-DowncastOnProjection` because variant flow tracks root Vars only. Users must extract to a local first (`let t = a[i]; t match { ... }`) or wrap the decode in a helper fn that takes the value by parameter. Fixable by either (a) copying/moving the projection into a fresh local during HLL lowering or (b) extending variant flow to track projections.
- **Generics in the MIR — remaining.** All checker + elab passes are in, monomorphization is in (`src/mir/mono`), and codegen emits LLVM quoted names for mono'd instantiations. Only conditional marker declarations (`Foo<T>: Copy where T: Copy`) are still deferred behind the unconditional-bounds form; the inline form on the decl and a separate `impl`-style form will coexist.
- **Conditional HLL marker bounds.** (`impl<T: Copy> Copy for Foo<T> {}`).
- **Array index and array length should be `u64`.** Today `place[operand]`
  and `[T; N]` both use `i64` in the parser and checker, mirroring MIR
  integers. Sizes and offsets are inherently non-negative — matches
  `$sizeof<T>` returning `u64`. Switch `TypeKind::Array(inner, size: u64)`
  and the index operand's expected type to `u64`. Ripples through the
  array-lit codegen (`getelementptr ..., i64 0, i64 i`) and every
  fixture that indexes an array with an `i64` literal.
- **Decide how `bool`-driven reachability is analyzed.** Today `branch(true)`/`branch(false)` don't get folded, so trivially-dead arms count as reachable. Either add a small constant-folding pass over `bool` operands, or reify `bool` as an enum so `variant_flow` handles it uniformly. Blocks tighter dead-arm warnings and short-circuit const evaluation. Decision + fixture.

## Lifetime checker gaps (semantic)
- **Bound-RHS lifetimes must be declared params.** `<'a: 'b>` requires
  `'b` in the same `<>` list; Rust auto-introduces bound-only names.
  Silica keeps this explicit — arguably fine, but worth documenting.
- **Call-site handling ignores fn pointers.** `Const::FnName` matches; `copy fn_ptr(args)` doesn't. Silent hole. Needs first-class fn-value lifetime tracking (`TypeKind::Fn` doesn't carry lifetime bounds today). The variance machinery is already pre-wired for this: `Variance::Covariant` and its `combine`/`emit_variance` branches encode the standard `fn(X) -> Y` composition rule (contravariant in X, covariant in Y), but nothing constructs `Covariant` because `walk_call_regions` doesn't descend into `TypeKind::Fn`.
- **`walk_ref_paths` and `walk_regions` skip `TypeKind::Array`.** Owned `[&mut T; N]` slots aren't added to the NLL borrower set or assigned per-slot regions. Sound because loan tracking still catches conflicts and place-state materialises RefState lazily on access, but NLL won't insert `unborrow a[k]` on last-use and inter-fn lifetime constraints don't flow through array slots. Fix when arrays appear in signatures with lifetime arguments.
- **No fixture for the nested-ref `&&i64` case or shared-ref returns read multiple times.** Adversarial coverage gap; adversarial testing after-commit rule should catch these when the next lifetime feature lands. A lifetime-bearing generic wrapper in a fn signature is covered by `View<'a, T>` in `hll_temporary_lifetimes_ok.si`.

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

## Diagnostics roadmap

The target architecture is to retain semantic values and complete source
provenance until the final diagnostic-rendering boundary. Passes should emit
typed failure payloads rather than already-formatted prose, but each pass owns
its payloads and wording; there should not be a central compiler-wide error
enum or a single sentence template forced onto unrelated failures.

Implement this as the following sequence of reviewable commits:

1. **Introduce typed failure payloads for MIR type checking.** Add a
   pass-local payload enum whose variants carry values such as `Type`, place,
   declaration name, and arity until rendering. Reuse small semantic payloads
   such as `Mismatch<T> { expected, found }`, and introduce a `UserOrdinal`
   type constructed from zero-based compiler indices so diagnostics cannot
   print "argument 0" or the wrong array-element position. Derive
   `TypeCheckCode` from the payload with an exhaustive match and render types
   through `DiagnosticFormat`; migrated call sites must not accept arbitrary
   preformatted mismatch strings. Migrate the complete MIR type-check family
   so the invariant is enforced throughout the pass, then pin consistent
   sentence-case, `expected ..., found ...` output in its fixtures.

2. **Make diagnostic context source-bearing.** Replace the string-only block
   context with a structured context carrying both the block label and its
   `SourceInfo`. Continue showing source-written MIR labels, but suppress or
   describe compiler-generated edge-split labels instead of exposing names
   such as `$edge0`. Keep this context separate from the primary
   diagnostic source: one identifies the enclosing scope, the other identifies
   the operation being blamed.

3. **Give MIR syntax below a statement precise provenance without changing
   semantic identity.** Design a shared source-bearing representation for the
   parsed/lowered occurrences of operands, rvalues, and place projections.
   Dataflow keys and semantic `Place` equality must not depend on source
   location. Land the data-model change first, then audit parser, pretty
   printer, helpers, type checking, elaborators, monomorphization, and codegen.
   Add parser and HLL-lowering tests proving written and generated nested nodes
   retain the correct `SourceInfo`; do not change diagnostic wording in this
   prerequisite commit.

4. **Use nested MIR provenance for precise primary and secondary spans.** Move
   call-argument mismatches, array-element mismatches, invalid dereferences,
   indexes, and projections from whole-statement spans to the exact offending
   syntax. Where a relationship matters, retain the use site as primary and
   attach the declaration or expected type as a labeled secondary source.
   Extend the focused diagnostic-span fixtures with both written MIR and HLL-
   generated cases.

5. **Add diagnostic hygiene guards, then migrate other families only from
   evidence.** Assert semantic invariants at construction/formatting boundaries:
   user errors have useful sources, diagnostic type formatting does not expose
   inference variables such as `?0`, generated temporary/block names are not
   shown as user identifiers, and user-facing positions are one-based. Migrate
   lifetime, init-state, or substructural diagnostics to typed payloads only
   when a fixture audit finds repeated message shapes, inconsistent rendering,
   or semantic data being discarded before formatting. Keep each pass in a
   separate commit.

**Stop condition:** items 1–4 address enforceable construction and lost
provenance and are worth completing. After the hygiene guards in item 5, do
not migrate one-off diagnostics merely for uniformity. If a pass has stable
fixtures, preserves its semantic data and sources, and has no repeated
formatting drift, further abstraction is diminishing-return work.

## Compiler consistency roadmap

These are targeted repairs for demonstrated drift mechanisms: semantic
identity encoded as display text, duplicated structural walks, and malformed
generic applications represented as ordinary valid data. Keep the changes
reviewable and fixture-backed; do not parameterize or duplicate `Program` by
pipeline phase. The existing `verify_no_take` boundary and downstream invariant
panics are intentional and sufficiently covered.

Implement the repairs in this order:

1. **Backfill elided Custom lifetimes, then make instantiation validated data.**
   Elision currently adds lifetime parameters for unannotated refs but leaves
   bare Custom self-mentions and local types with zero lifetime arguments. First
   make elision two-pass: determine each declaration's final lifetime
   parameters, then materialize fresh arguments at every bare Custom use and add
   them to the containing scope. Once zero arguments are no longer ambiguous,
   require exact lifetime and type arity.

   Replace parallel parameter/argument slices at substitution sites with
   structured generic arguments and an `Instantiation` constructible only
   after the applicable arities validate. Custom types validate both lifetime
   and type arguments; `FnName` validates its explicit type arguments while
   call-region inference remains a separate lifetime operation. Valid-path
   substitution must be total and must not return the original type on
   mismatch. Diagnostic continuation must use a separately named recovery API
   and only after recording the construction error; later semantic passes
   should consume validated instantiations or skip malformed uses. Migrate
   field/downcast projection, function references, enum construction,
   lifetime-region expansion, and monomorphization, with interaction fixtures
   proving malformed uses do not suppress independent diagnostics.

   Keep this reviewable as four commits: (a) two-pass elision and Custom
   lifetime backfill, (b) the validated argument/instantiation data model and
   unit tests, (c) type-environment and checker migration with explicit
   recovery diagnostics, and (d) downstream lifetime/monomorphization
   migration plus interaction fixtures. Do not combine the prerequisite with
   caller migration merely to keep the intermediate API private.

2. **Centralize place projection semantics.** Build one lossless, exhaustive
   decomposition/reconstruction library over `Place` and its projection
   steps. Derive explicit queries for owned paths, statically trackable paths,
   dereference-containing paths, loan paths, and initialization paths instead
   of maintaining pass-local recursive interpretations. Preserve dynamic
   index operands losslessly, and require every new `Place` variant to update
   the central projection library before downstream passes compile.

3. **Use typed initialization slots.** Replace string-keyed
   `InitState::Partial` entries with distinct field and constant-index keys;
   array indices must remain integers throughout analysis and only be rendered
   as text at the diagnostic or pretty-print boundary. Rebuild init-state,
   overwrite, leak, and drop-elaboration walks on those typed slots.

4. **Finish lifetime traversal without sentinels or eager array expansion.**
   Replace the `Region::Free(u32::MAX)` unresolved-region sentinel with an
   explicit resolution result or region category. Make all lifetime type walks
   descend arrays consistently, but do not allocate one region entry for every
   element of an arbitrary `u64`-length array. Materialize per-slot state from
   actually referenced constant-index places, while signature-level lifetime
   flow traverses the element type structurally. Add positive and negative
   fixtures for reference-bearing arrays, constant slots, dynamic slots, and
   inter-function constraints.

The function-type loss of ABI and lifetime-signature information remains a
feature prerequisite under FFI/lifetime work rather than part of this cleanup.
Likewise, phase-specific `Program` wrappers are deliberately out of scope.

### Cross-roadmap execution order

When diagnostics and consistency work are interleaved, use this dependency
order rather than completing either roadmap in isolation:

1. Consistency 1 before Diagnostics 1: establish validated instantiation and
   explicit recovery before type-check payloads depend on those failures.
2. Consistency 2 before Diagnostics 3–4: centralize semantic place projections
   before adding occurrence provenance, so the large provenance refactor has
   one projection boundary to update rather than many pass-local walkers.
3. Consistency 3–4: move init-state and lifetime analyses onto the new typed
   projection/type foundations.
4. Diagnostics 2–5: finish source-bearing context and syntax, precise spans,
   and hygiene guards. Diagnostics 5 remains the stop point for abstraction
   that is not justified by a concrete inconsistency or lost semantic datum.

Diagnostics 1 may initially retain statement-level sources; Diagnostics 4 is
the deliberate later refinement to nested operand and projection sources.

## FFI
- **`TypeKind::Fn` erases ABI.** A `fn(T) -> R`-typed value carries no ABI info, so calling through a fn pointer can't dispatch Silica-sret vs C-ABI. Once C-ABI externs are wired through codegen (see the extern ABI item under Language features), a fn pointer taken to an extern would need either a Silica-shape wrapper or a ban at the pointer-taking site.

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
