# Silica examples

Canonical Silica programs that exercise the pipeline end-to-end.

- `factorial.sim` — recursive factorial in MIR with a `main` entry
  point. Compile with `--llvm` to get LLVM IR that (after `llc` +
  `clang`) exits with code 120.
- `option_match.si` — HLL surface syntax showing enum declaration,
  postfix `match`, `Name::Variant(payload)` construction, and how
  the lowered MIR looks after elaboration.

## Running

```
cargo run --quiet -- examples/factorial.sim          # pretty-print elaborated MIR
cargo run --quiet -- --llvm examples/factorial.sim   # emit LLVM IR
cargo run --quiet -- examples/option_match.si        # HLL → elaborated MIR
```

`.si` files run through the HLL frontend (parse + type-check +
mutability check + lowering) before entering the MIR pipeline.
`.sim` files skip straight to MIR.
