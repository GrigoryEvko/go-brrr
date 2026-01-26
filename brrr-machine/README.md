# brrr-machine

Formally verified static analysis framework in F*.

This is the F* implementation of the brrr-machine analyzer - the core analysis
engine with mechanically verified soundness properties. The specifications and
proofs are written in F*, with runtime implementations in Rust (see brrr-cli).

## Project Structure

```
brrr-machine/
├── src/                    # F* source code
│   ├── analysis/           # Analysis algorithms
│   │   ├── IFDS.fst        # IFDS framework (Reps et al. 1995)
│   │   ├── IFDS.fsti       # IFDS interface specification
│   │   ├── IFDSTaint.fst   # Taint analysis on IFDS
│   │   ├── IFDSTaint.fsti  # Taint interface specification
│   │   ├── Dataflow.fst    # Generic dataflow framework
│   │   ├── GaloisConnection.fst  # Abstract interpretation foundation
│   │   ├── IncrementalTaint.fst  # Incremental analysis (Adapton-style)
│   │   └── Taint.fst       # Basic taint analysis
│   │
│   ├── cpg/                # Code Property Graph
│   │   └── CPG.fst         # Unified program representation
│   │
│   ├── query/              # Graph query language
│   │   └── Traversal.fst   # CPG traversal operations
│   │
│   ├── core/               # Core types (placeholder)
│   ├── security/           # Security analyses (placeholder)
│   ├── lang/go/            # Go language support (placeholder)
│   │
│   ├── Demo.fst            # Demo module
│   ├── Makefile            # F* build configuration
│   └── README.md           # Source documentation
│
├── papers/                 # Research paper notes (gitignored)
├── reviews/                # Paper reviews (gitignored)
├── synthesis/              # Synthesis documents (gitignored)
│
├── LICENSE                 # Apache-2.0
└── README.md               # This file
```

## Key Modules

### Analysis Framework

| Module | Lines | Description |
|--------|-------|-------------|
| `IFDS.fst` | 2,166 | IFDS algorithm with context-sensitive interprocedural analysis |
| `IFDSTaint.fst` | 3,328 | Taint analysis built on IFDS framework |
| `GaloisConnection.fst` | 1,786 | Abstract interpretation with Galois connections |
| `Dataflow.fst` | 1,037 | Generic monotone dataflow framework |
| `IncrementalTaint.fst` | 1,821 | Adapton-style incremental taint analysis |

### Code Property Graph

| Module | Lines | Description |
|--------|-------|-------------|
| `CPG.fst` | 1,264 | Unified CPG combining AST, CFG, PDG, CallGraph |
| `Traversal.fst` | 1,137 | Graph traversal and query operations |

## Verification Status

**Total: 14,711 lines of F* code**

**Admits: 0** - All proofs are complete (no `admit()` calls)

The codebase follows HACL*/EverParse patterns:
- Interface files (.fsti) for public APIs
- Z3 options: `--z3rlimit 50 --fuel 0 --ifuel 0`
- Explicit pre/post conditions on all operations
- Three-valued logic (TMaybe) for may/must analysis

## Building

Requires F* (https://github.com/FStarLang/FStar)

```bash
cd src/

# Verify all modules
make verify

# Extract to OCaml
make extract

# Clean build artifacts
make clean

# Show statistics
make stats
```

## Theoretical Foundation

Based on foundational papers:

- **IFDS**: Reps, Horwitz, Sagiv 1995 - "Precise Interprocedural Dataflow Analysis via Graph Reachability"
- **Taint Analysis**: Livshits 2005, Arzt 2014 (FlowDroid)
- **Abstract Interpretation**: Cousot & Cousot 1977
- **CPG**: Yamaguchi 2014 - "Modeling and Discovering Vulnerabilities with Code Property Graphs"
- **Incremental Analysis**: Hammer 2014 (Adapton)

## Architecture

```
                    ┌─────────────────────────────────────┐
                    │         brrr-machine (F*)           │
                    │                                     │
                    │  ┌─────────────┐  ┌─────────────┐  │
                    │  │  Analysis   │  │    CPG      │  │
                    │  │  (IFDS,     │  │  (Unified   │  │
                    │  │  Dataflow)  │  │  Graph)     │  │
                    │  └─────────────┘  └─────────────┘  │
                    │         │                │         │
                    │         └───────┬────────┘         │
                    │                 │                  │
                    │         ┌───────▼────────┐         │
                    │         │    Query       │         │
                    │         │  (Traversal)   │         │
                    │         └────────────────┘         │
                    └─────────────────────────────────────┘
                                     │
                                     │ Verified Interface
                                     ▼
                    ┌─────────────────────────────────────┐
                    │         brrr-cli (Rust)             │
                    │         Runtime implementation       │
                    └─────────────────────────────────────┘
```

## License

Apache-2.0
