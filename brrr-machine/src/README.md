# BrrrMachine F* Implementation

Formal specification and verified implementation of the brrr-machine static analyzer.

## Structure

```
src/
├── core/               # Core types and infrastructure
│   ├── Types.fst       # IR types, expressions, statements
│   ├── CFG.fst         # Control flow graph
│   └── CallGraph.fst   # Call graph construction
│
├── analysis/           # Analysis passes
│   ├── Dataflow.fst    # Generic dataflow framework
│   └── Taint.fst       # Taint analysis
│
├── security/           # Security-specific analyses
│   └── SQLInjection.fst # SQL injection detection
│
└── lang/               # Language-specific modules
    └── go/             # Go language support
        ├── Parser.fst   # Go parsing specification
        └── Builtins.fst # Go built-in functions
```

## Building

Requires F* (https://github.com/FStarLang/FStar)

```bash
# Verify all modules
make verify

# Extract to OCaml
make extract
```

## Module Dependency Order

1. `BrrrMachine.Core.Types` - No dependencies
2. `BrrrMachine.Core.CFG` - Depends on Types
3. `BrrrMachine.Core.CallGraph` - Depends on Types
4. `BrrrMachine.Analysis.Dataflow` - Depends on Core
5. `BrrrMachine.Analysis.Taint` - Depends on Dataflow
6. `BrrrMachine.Security.*` - Depends on Analysis
7. `BrrrMachine.Lang.*` - Depends on Core

## Design Principles

### Types as Specifications

F* refinement types encode invariants:

```fstar
(* Variable must have valid type *)
type typed_var = v:var_id{has_type v}

(* CFG edge must connect existing nodes *)
type valid_edge (g: cfg) = e:cfg_edge{
  node_exists g e.edge_src /\
  node_exists g e.edge_dst
}
```

### Lemmas as Theorems

Soundness properties are expressed as lemmas:

```fstar
(* Taint analysis has no false negatives *)
val taint_sound :
  g:cfg ->
  result:taint_result{result = analyze_taint g} ->
  path:concrete_path{reaches_sink path} ->
  Lemma (path_detected result path)
```

### Verified by Construction

Core algorithms are proven correct by F* type-checking:

- `admit()` = unverified (placeholder)
- No `admit()` = verified by F*

## Current Status

| Module | Verified | Notes |
|--------|----------|-------|
| Types.fst | Partial | Types defined, some `admit()` |
| CFG.fst | Partial | Structure ok, algorithms placeholders |
| CallGraph.fst | Partial | Basic structure |
| Dataflow.fst | Partial | Framework defined, theorems `admit()` |
| Taint.fst | Partial | Go sources/sinks defined |
| SQLInjection.fst | Partial | Detection logic, needs integration |
| Parser.fst | Specification | Actual parsing in Rust |
| Builtins.fst | Complete | Reference data |

## Next Steps

1. **Verify Dataflow**: Prove lattice laws and fixed-point convergence
2. **Verify Taint**: Prove soundness (no false negatives)
3. **Add IFDS**: Implement IFDS algorithm with proofs
4. **Add More Languages**: TypeScript, Rust support
