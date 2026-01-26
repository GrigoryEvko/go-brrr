# BrrrMachine F* Implementation

Formal specification and verified implementation of the brrr-machine static analyzer.

## Structure

```
src/
├── analysis/               # Analysis algorithms
│   ├── IFDS.fst            # IFDS framework (Reps et al. 1995)
│   ├── IFDS.fsti           # IFDS interface
│   ├── IFDSTaint.fst       # Taint analysis on IFDS
│   ├── IFDSTaint.fsti      # Taint interface
│   ├── Dataflow.fst        # Generic dataflow framework
│   ├── GaloisConnection.fst # Abstract interpretation
│   ├── IncrementalTaint.fst # Adapton-style incremental
│   └── Taint.fst           # Basic taint analysis
│
├── cpg/                    # Code Property Graph
│   └── CPG.fst             # Unified program representation
│
├── query/                  # Query layer
│   └── Traversal.fst       # CPG traversal operations
│
├── Demo.fst                # Demo module
├── Makefile                # F* build configuration
└── README.md               # This file
```

## Building

Requires F* (https://github.com/FStarLang/FStar)

```bash
# Verify all modules
make verify

# Extract to OCaml
make extract

# Show statistics
make stats

# Clean build artifacts
make clean
```

## Module Dependencies

```
CPG.fst
   │
   ├───► Traversal.fst
   │
   └───► Dataflow.fst ───► Taint.fst
                │
                └───► IFDS.fst ───► IFDSTaint.fst
                         │
                         └───► IncrementalTaint.fst

GaloisConnection.fst (standalone abstract interpretation foundation)
```

## Verification Status

| Module | Lines | Interface | Status |
|--------|-------|-----------|--------|
| CPG.fst | 1,264 | - | Verified |
| Traversal.fst | 1,137 | - | Verified |
| Dataflow.fst | 1,037 | - | Verified |
| Taint.fst | 366 | - | Verified |
| GaloisConnection.fst | 1,786 | - | Verified |
| IFDS.fst | 2,166 | IFDS.fsti | Verified |
| IFDSTaint.fst | 3,328 | IFDSTaint.fsti | Verified |
| IncrementalTaint.fst | 1,821 | - | Verified |

**Total: ~14,700 lines of F* | 0 admits | Fully verified**

## Design Patterns (Following HACL*/EverParse)

### Z3 Options

All modules use conservative Z3 settings:
```fstar
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"
```

### Interface Files (.fsti)

Public APIs have interface files declaring:
- Type signatures with refinements
- Pre/post conditions
- Abstract type definitions

### Three-Valued Logic (TMaybe)

May/must analysis uses three-valued logic:
```fstar
type tmaybe =
  | TDefinitely  (* Must hold *)
  | TMaybe       (* May hold *)
  | TNo          (* Does not hold *)
```

## Key Algorithms

### IFDS (Reps et al. 1995)

Context-sensitive interprocedural dataflow via graph reachability:
- Exploded supergraph construction
- Path edges and summary edges
- O(ED^3) complexity

### Galois Connections

Abstract interpretation foundation:
- Lattice operations with verified laws
- Widening/narrowing for termination
- Soundness by construction

### Incremental Analysis

Adapton-style self-adjusting computation:
- Dependency tracking
- Incremental recomputation on change
- Efficient re-analysis for IDE integration
