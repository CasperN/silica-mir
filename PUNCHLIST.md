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
- **Generics in the MIR — remaining.** All checker + elab passes are in, monomorphization is in (`src/mir/mono`), and codegen emits LLVM quoted names for mono'd instantiations. Only conditional marker declarations (`Foo<T>: Copy where T: Copy`) are still deferred behind the unconditional-bounds form; the inline form on the decl and a separate `impl`-style form will coexist.
- **Conditional HLL marker bounds.** (`impl<T: Copy> Copy for Foo<T> {}`).
- **Array indices should be `u64`.** Array lengths are represented as
  `u64` in both HLL and MIR, but `place[operand]` still accepts any integer
  type. Sizes and offsets are inherently non-negative, matching
  `$sizeof<T>` returning `u64`. Require the index operand to be `u64` and
  update fixtures that still index arrays with `i64` values.
- **Retire remaining `variant_flow.rs`.** `SwitchArmFalselyUnreachable` / `SwitchArmDeadCode` now live in `reachability` alongside bool-const branch folding; the remaining `SwitchNoArms` / `SwitchNotExhaustive` / `SwitchDuplicateArm` still live in `variant_flow.rs` because they need dead-block filtering. Move them into `reachability` (they can reuse its reachable-blocks set) and delete `variant_flow.rs` + `DiagCode::VariantFlow`. `DowncastVariantNotRefined` — the last `VariantFlowCode` — is emitted by `place_state` today; it can move to a place_state-owned code enum in the same pass.

## Lifetime checker gaps (semantic)
- **Fn-pointer lifetime tracking.** `Const::FnName` calls have lifetime
  tracking; `copy fn_ptr(args)` doesn't. Silent hole. Prerequisite: extend
  `TypeKind::Fn` with per-slot lifetime bounds — the variance machinery
  (`Variance::Covariant`, `combine`, `emit_variance`) is already pre-wired
  for the standard `fn(X) -> Y` composition (contravariant in X, covariant
  in Y). Once `TypeKind::Fn` carries the metadata, `walk_call_regions`
  needs a Fn-variant arm.

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

1. **Close missing-descent gaps in MIR walkers.** The remaining hand-rolled
   type walks skip specific variants and diverge in ways the type checker
   can't catch. Fix each in a separate commit; extract shared recursion
   only when two or more walkers demonstrably duplicate it.
   - `region::walk_ref_places` — the shared traversal now consumed by
     `build_region_ctx` and `collect_borrowers`; must descend
     `TypeKind::Array` so owned `[&mut T; N]` slots are added to the NLL
     borrower set and inter-fn lifetime constraints flow through array
     slots. Adding Array descent interacts with Consistency 5's
     per-slot-region strategy. Drop-elab's `walk_diverged` array/enum
     Custom descent is tracked separately under Consistency 4.

2. **Backfill elided Custom lifetimes, then make instantiation validated data.**
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

3. **Centralize place projection semantics.** Build one lossless, exhaustive
   decomposition/reconstruction library over `Place` and its projection
   steps. Derive explicit queries for owned paths, statically trackable
   paths, dereference-containing paths, loan paths, and initialization
   paths instead of maintaining pass-local recursive interpretations.
   Preserve dynamic index operands losslessly, and require every new
   `Place` variant to update the central projection library before
   downstream passes compile.

4. **Extend `walk_diverged` to array slots.** `InitState::Partial` is now
   keyed by `InitSlot::{Field, Index}`, but `walk_diverged` still returns
   without emitting drops for `TypeKind::Array` — partially-initialized
   arrays fall through to the final `check_return_leaks` sweep instead of
   getting per-slot edge drops. Enums stay atomic (whole-value
   construction / whole-value move), so no variant-level descent is
   needed; only the array arm is a real gap.

5. **Finish lifetime traversal without sentinels or eager array expansion.**
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

1. Consistency 1 first: close the missing-descent gaps and consolidate any
   demonstrable walker duplication so downstream migrations aren't chasing
   the same variant additions across pass-local walks.
2. Consistency 2 before Diagnostics 1: establish validated instantiation and
   explicit recovery before type-check payloads depend on those failures.
3. Consistency 3 before Diagnostics 3–4: centralize semantic place projections
   before adding occurrence provenance, so the large provenance refactor has
   one projection boundary to update rather than many pass-local walkers.
4. Consistency 4–5: move init-state and lifetime analyses onto the new typed
   projection/type foundations.
5. Diagnostics 2–5: finish source-bearing context and syntax, precise spans,
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
