# brrr-lang

F* specification for the Brrr-Lang Code IR (Intermediate Representation).

This is a formal specification written in F*, a proof-oriented programming language. It is NOT a Rust crate or executable compiler - it defines the semantics and type system that guide the implementation.

## Prerequisites

- **F\* compiler** (fstar.exe) version 2024.01.13 or later
- **Z3 SMT solver** version 4.8.5 or later (for proof verification)

### Installation

F* can be installed from source or via OPAM:

```bash
# Via OPAM (recommended)
opam install fstar

# Or build from source
git clone https://github.com/FStarLang/FStar.git
cd FStar && make -j
```

## Project Structure

```
brrr-lang/
├── Makefile              # Top-level build configuration
├── brrr_lang_spec.md     # Language specification document
├── brrr_lang_spec_v0.4.pdf
├── brrr_lang_spec_v0.4.tex
├── src/
│   ├── Makefile          # Source-level build rules
│   ├── core/             # Core type system and semantics
│   ├── translation/      # Multi-language translation specs
│   ├── analysis/         # Static analysis specifications (planned)
│   ├── security/         # Security type specifications (planned)
│   ├── physical/         # Physical representation specs (planned)
│   └── lang/             # Language-specific modules (planned)
└── tests/                # F* test modules
```

## Module Overview

### Core Modules (src/core/)

| Module | Description |
|--------|-------------|
| `Primitives.fst(i)` | Primitive types (int, float, etc.) |
| `Modes.fst(i)` | Type modes (owned, borrowed, shared) |
| `Effects.fst(i)` | Effect algebra and row types |
| `BrrrTypes.fst(i)` | Main type system (12 type constructors) |
| `Expressions.fst(i)` | Expression AST and well-formedness |
| `Values.fst(i)` | Value representation |
| `Eval.fst(i)` | Operational semantics |
| `Kinds.fst(i)` | Kind system for higher-kinded types |
| `TypeChecker.fst(i)` | Bidirectional type checking |
| `BorrowChecker.fst(i)` | Ownership and borrow checking |
| `DependentTypes.fst(i)` | Dependent type support |
| `SessionTypes.fst(i)` | Session types for protocols |
| `MultipartySession.fst(i)` | Multiparty session types |
| `SecurityTypes.fst(i)` | Information flow types |
| `TaintAnalysis.fst(i)` | Taint tracking |
| `PropositionalEquality.fst(i)` | Type equality proofs |

### Translation Modules (src/translation/)

| Module | Description |
|--------|-------------|
| `TranslationSpec.fst(i)` | Multi-language translation framework |
| `PythonTranslation.fst(i)` | Python-to-IR translation |
| `PythonTypes.fst` | Python typing module support |

### Test Modules (tests/)

| Module | Description |
|--------|-------------|
| `TestBorrowChecker.fst` | Borrow checker tests |
| `TestSessionTypes.fst` | Session type tests |
| `TestLattices.fst` | Effect lattice tests |
| `TestTranslations.fst` | Translation tests |

## Building

```bash
# Verify all core modules (extensive - for CI/release)
make verify

# Quick verification (for development)
make quick

# Verify a single file
make check F=src/core/BrrrTypes.fst

# Quick check a single file
make check-quick F=src/core/BrrrTypes.fst

# Generate dependencies
make depend

# Clean build artifacts
make clean

# Full rebuild
make world
```

## Z3 Configuration

The Makefile configures Z3 for verification. Key parameters:

| Parameter | Default | Purpose |
|-----------|---------|---------|
| `Z3_RLIMIT` | 500 | Z3 resource limit (seconds) |
| `FUEL` | 8 | Recursive function unfolding depth |
| `IFUEL` | 4 | Inductive type unfolding depth |

For quick development iteration, use `make quick` which reduces these limits.

## Editor Integration

For Emacs with fstar-mode.el, the Makefile provides:

```bash
# Get F* flags for current file
make src/core/BrrrTypes.fst-in
```

## Design Principles

This specification follows patterns from established F* projects:

- **HACL\***: Interface/implementation separation (.fsti/.fst), Z3 tuning
- **EverParse**: Source location tracking, environment threading

Key design decisions:

1. **12 type constructors** for SMT tractability (reduced from 27)
2. **noeq types** for recursive structures containing functions
3. **Effect rows** forming a bounded join-semilattice
4. **Bidirectional type checking** for inference
5. **Ownership modes** for memory safety

## License

Apache-2.0. See [LICENSE](LICENSE).

## Related

- [brrr-repr](../brrr-repr/) - Rust implementation of the IR
- [brrr-cli](../brrr-cli/) - Command-line tool
