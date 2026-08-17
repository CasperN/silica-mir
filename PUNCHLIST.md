# Punch list

Deferred work and known gaps. Items get added, refined, and closed as
the compiler evolves; treat entries as snapshots, not commitments.

## Language features
- **Complete HLL trait and method use.** Keep this work split into independently
  reviewable changes, in dependency order:
  1. Complete the function ABI and linkage roadmap below.
  2. Revisit which ownership traits are compiler-blessed. The trivial and auto
     tiers require compiler interaction; the higher explicit tiers may live in
     the standard library. Discuss the boundary before implementation.
- **Standardize `&drop` vs `&deinit`.** Same reference kind
  (`RefKind::Drop`) has two surface names — MIR uses `&drop`, HLL uses
  `&deinit`. Every fixture author, diagnostic reader, and agent has
  to remember the mapping. Pick one across both surfaces (or make one
  a strict alias) and delete the other.
- **Conditional traits and markers**
- **Generic parameter position on decls.** MIR puts generics between the
  keyword and the name (`fn<T> foo`, `struct<T> Box`, `trait<T> Iter`).
  Rust convention is post-name (`fn foo<T>`, `struct Box<T>`, `trait Iter<T>`).
  Consider moving to the post-name position across both HLL and MIR
  grammars — cheaper authoring cost, matches every other language readers
  are used to. Grammar change + fixture regen; no semantics move.
- **Extract a common `instance` grammar rule.** Multiple grammar sites
  ("identifier + optional type_args") already share the shape: `fn_name`'s
  free-fn form, the trait ref inside `impl_decl` (`trait_name` +
  `type_args`), the trait/method halves of `fn_name`'s UFCS form, and
  the enum-construction rvalue. Extract to `common.grammar.js`'s shared
  rule set so all four sites route through one node kind. Parser
  wrappers collapse into a single `map_instance` helper.
- Decide on and standardize on whether malloc size and array index type should be signed or unsigned.

## Lifetime checker gaps (semantic)
- **Fn-pointer lifetime tracking.** `Const::FnName` calls have lifetime
  tracking; `copy fn_ptr(args)` doesn't. Silent hole. Prerequisite: extend
  `TypeKind::Fn` with per-slot lifetime bounds — the variance machinery
  (`Variance::Covariant`, `combine`, `emit_variance`) is already pre-wired
  for the standard `fn(X) -> Y` composition (contravariant in X, covariant
  in Y). Once `TypeKind::Fn` carries the metadata, `walk_call_regions`
  needs a Fn-variant arm.

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

Keep the changes reviewable and fixture-backed; do not parameterize or
duplicate `Program` by pipeline phase. The existing `verify_no_take`
boundary and downstream invariant panics are intentional and sufficiently
covered.

1. **Centralize place projection semantics.** Build one lossless, exhaustive
   decomposition/reconstruction library over `Place` and its projection
   steps. Derive explicit queries for owned paths, statically trackable
   paths, dereference-containing paths, loan paths, and initialization
   paths instead of maintaining pass-local recursive interpretations.
   Preserve dynamic index operands losslessly, and require every new
   `Place` variant to update the central projection library before
   downstream passes compile.

The function-type loss of lifetime-signature information remains a feature
prerequisite under lifetime work rather than part of this cleanup. Function
ABI representation is owned by the ABI and linkage roadmap below.
Likewise, phase-specific `Program` wrappers are deliberately out of scope.

### Cross-roadmap execution order

When diagnostics and consistency work are interleaved, use this dependency
order rather than completing either roadmap in isolation:

1. Consistency 1 before Diagnostics 3–4: centralize semantic place projections
   before adding occurrence provenance, so the large provenance refactor has
   one projection boundary to update rather than many pass-local walkers.
2. Diagnostics 2–5: finish source-bearing context and syntax, precise spans,
   and hygiene guards. Diagnostics 5 remains the stop point for abstraction
   that is not justified by a concrete inconsistency or lost semantic datum.

Diagnostics 1 may initially retain statement-level sources; Diagnostics 4 is
the deliberate later refinement to nested operand and projection sources.

## Function ABI and linkage roadmap

Treat three properties independently throughout the compiler:

- `extern` says that a declaration is supplied by another linkage unit rather
  than by a Silica body.
- An ABI modifier such as `"C"` selects a calling convention. Its absence
  selects the native Silica convention.
- `unsafe` controls the obligations at a call site.

The ABI is part of a callable value's type. Linkage and body availability are
properties of a declaration, not of a function type. Trait signatures have no
body but are not external declarations; impl methods have bodies but may use a
non-default ABI.

Implement this as the following sequence of independently reviewable commits:

1. **Separate and centralize declaration modifiers.** Introduce one shared ABI
   representation for HLL and MIR declarations, and stop inferring `extern`
   from the presence or absence of a body. Parse and pretty-print linkage, ABI,
   and safety independently, preserve them through HLL lowering, and diagnose
   structurally invalid declaration/body combinations. Keep the default native
   ABI behavior unchanged. Pin round trips and both bodyful and bodyless free
   functions in fixtures.

2. **Make function types ABI-bearing and calls type-directed.** Extend HLL and
   MIR function types with the ABI, including surface syntax, formatting,
   inference, unification, substitution, folding, monomorphization, and
   function-item typing. ABI mismatches must be ordinary type errors. Refactor
   codegen so direct and indirect calls select return and argument conventions
   from the callee type rather than recovering them from a direct declaration.
   Cover native and C-ABI declarations, definitions, function values, indirect
   calls, and non-unit returns end to end in the same commit.

3. **Apply ABI rules uniformly to methods.** Accept ABI modifiers on trait,
   inherent, and trait-impl methods; reject unsupported ABI names everywhere;
   require an impl method's ABI to match its trait signature; and preserve the
   selected method ABI through qualified calls, dot calls, lowering, and
   monomorphization. Test inherent and trait dispatch, generic receivers,
   receiver auto-borrowing, explicit qualified calls, and ambiguity/error
   diagnostics without introducing ABI-specific method resolution paths.

**Stop condition:** free functions, methods, and first-class function values
retain their ABI through parsing, checking, lowering, monomorphization, and
codegen; direct and indirect calls agree; and invalid or mismatched ABIs are
diagnosed before codegen. Platform-specific C ABI classification, variadics,
symbol visibility, dynamic linking, and target-specific LLVM parameter
attributes remain later FFI work.

## Standard library roadmap

Use `tests/programs/stdlib.si` as the executable design probe. Keep library
APIs honest about safety and ownership, and land compiler prerequisites as
independent, fixture-backed changes in this order:

1. **Support static methods.** `Box::new(x)` should be interpreted as a static
   method on `Box<T>`; however, it is currently parsed as an enum variant constructor. 
2. **`self` argument sugar**, `&self -> self: &Self` in argument position, and
   analogously for other ref kinds and account for lifetime params too.
3. **Transfer family blanket priority**: In the Transfer column (`AutoTransfer`,
   `Transfer`, `CoTransfer`), resolve competing implementations by:
   (1) User-defined specialized implementation (e.g. buffer swap override),
   (2) Vertical forwarding implementation (`AutoTransfer => Transfer => CoTransfer`),
   (3) Horizontal synthesized fallback (`Clone + Destroy => Transfer`).

### Other clarity issues
- **`&deinit`**: We should delete all references to `deinit` and standardize on `&drop`.
- **Reference lifetime token ordering (`&'a drop T`)**: Reference keyword precedes lifetime (`&drop 'a T`). We should standardize on the Rust way.
- **Undeclared lifetime in method signatures**: When a method signature uses a lifetime not in scope (e.g. `self: &'a Self` without `fn<'a>`), emit an `UndeclaredLifetime` error at the method declaration rather than failing silently during receiver matching.
- **Field access on references**: When projecting `self.field` on reference types (`&Self`, `&drop Self`), suggest explicit dereferencing `self.*.field`.


## Testing gaps
- **Warning-only fixtures are not pinned.** A clean `.expected.sim` fixture
  compares only pretty-printed MIR, so warnings are discarded. Allow an
  explicit diagnostics expectation for programs that emit warnings but no
  errors, and make `UPDATE_EXPECT` preserve that choice rather than switching
  solely on `has_errors()`.
- **End-to-end runtime fixtures.** `tests/programs/*` today pins elaborated MIR, but real behavior — `sum_to_n(10) → 55`, `hello_world` prints `hi!\n`, linked-list `exit=6` — is only verified manually. Automate: compile to `.ll`, link any sibling C shim, execute, pin exit code + stdout in a `.run.expected`. Needs a new fixture-runner stage + `clang` gating. Bazel migration (see Longer term) is one path to the cross-language build infra this requires.

## Longer term
- **Bazel-based build with proper cross-language infra.** Today the compiler is `cargo`, and any cross-language wiring (LLVM IR emission → `clang` link → binary → runtime → check exit) is manual. A Bazel migration would let end-to-end runtime tests, C-shim linking, and future host-language integrations (LLVM tooling, wasm, cross-compile) be first-class build actions in a hermetic graph. The immediate motivator is the End-to-end runtime fixtures item in Testing gaps.
- **HLL tuples, anonymous enums** (`(left: T | right: U)`?), and a Rust-shaped enum syntax (currently only newtype-with-different-syntax).
- **No-alias raw pointer variant** (`*noalias T`) alongside the aliasing `*T`. Enables LLVM `noalias` on parameters where the checker can prove exclusivity.
- Standard library modules and multi-file packaging. The API and compiler
  prerequisites are tracked in the standard library roadmap above.
- Tighten MIR struct/enum decl separators from whitespace-or-comma
  to comma-required-optional-trailing (match HLL).
- Coroutines. Prerequisites: generics, lifetime arguments, HLL `defer`.
- Lambdas.
- Complete platform C FFI beyond call-convention selection: ABI classification
  for aggregate arguments and returns, variadics, symbol visibility, dynamic
  linking, and target-specific LLVM parameter attributes.
- Translation units and multi-file compilation: Support modular compilation, imports, symbol visibility, and linking of separate Silica source files.
- Forward-declared data structures: Support opaque/external struct declarations to safely pass un-sized external resources across FFI boundaries.

## Impl coherence
- Define crate ownership/orphan rules for trait implementations.
- Reject overlapping generic trait and inherent impls at declaration time,
  including overlaps that are never selected by a call. Extend this to an ODR
  across translation units.
- Diagnose impl parameters that cannot be inferred from the trait path or target
  instead of allowing every call to fail later with `TraitFnNoImpl`.

## First-class function types
- Audit and complete function values across checking, monomorphization, and
  codegen. This includes deciding how trait methods become function values;
  direct trait-method calls are currently the supported dispatch form.


## Compiler design
- To what exent should we unify the MIR and HLL AST?
  - Declarations seem to mostly be sharable. Sharing them might make the
  compiler simpler, especially if we eventually want a demand-driven, zig-like,
  architecture.
  - MIR uses `$return: &out T` instead of `-> T`
  - MIR has `$` prefixed identifers that are illegal in the HLL
  - MIR fn bodies are CFGs with no temporaries.
  - MIR has `move x` and `copy x` operands.


# Current Yak-shaving stack
- Complete HLL trait use
- Standard library
- Modules
- Standard `Span` and `Vec` types working properly 
- A standard `Box` type working properly
