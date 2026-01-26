# brrr-repr

Binary and text representation formats for the brrr-lang intermediate representation.

## Overview

`brrr-repr` provides the core data structures and serialization formats for the brrr-lang IR:

- **Types**: `BrrrType` with 12 variants (primitives, numerics, functions, structs, enums, etc.)
- **Expressions**: `Expr` with 53 variants covering all language constructs
- **Effects**: Row-polymorphic effect system with effect handlers
- **Modes**: Linear, affine, and relevant type tracking
- **Sessions**: Binary and multiparty session types for protocol verification
- **Verification**: Contracts, formulas, and verification condition generation

## File Formats

### Binary Format (`.brrr`)

Compact binary format for fast loading:

```
[MAGIC: "BRRR" (4 bytes)]
[VERSION: u16]
[MODULE_NAME: len + bytes]
[FILES: count + (len + bytes)*]
[STRING_TABLE: count + (len + bytes)*]
[TYPES: varint count + encoded types]
[EXPRS: varint count + encoded exprs]
[DECLARATIONS: varint count + encoded declarations]
[CONTENT_HASH: 16 bytes (xxh3)]
```

### Text Format (`.brrrx`)

Human-readable S-expression format for debugging:

```lisp
; brrr text format v1
(module "example"
  (files
    (0 "main.brrr"))
  (types
    (0 (prim Bool))
    (1 (func ((param x i32)) i32 (effects))))
  (exprs
    (0 (binary add (lit int 1 i32) (lit int 2 i32)))))
```

## Usage

```rust
use brrr_repr::{BrrrModule, BrrrEncoder, BrrrDecoder, Format};
use brrr_repr::types::{BrrrType, PrimKind};

// Create a module
let mut module = BrrrModule::new("example");
module.add_type(BrrrType::Prim(PrimKind::Bool));

// Encode to binary
let encoder = BrrrEncoder::from_module(module);
let mut buffer = Vec::new();
encoder.encode_binary(&mut buffer).unwrap();

// Decode from binary
let decoder = BrrrDecoder::decode_binary(&buffer[..]).unwrap();
let decoded = decoder.into_module();
```

## Modules

| Module | Description |
|--------|-------------|
| `types` | Type system: `BrrrType`, `NumericType`, `FuncType`, `StructType`, etc. |
| `expr` | Expressions: `Expr`, `Literal`, `Pattern`, operators |
| `effects` | Effect rows, effect operations, handlers |
| `modes` | Linear type tracking: `Mode`, `LinCtx` |
| `session` | Session types: binary and multiparty protocols |
| `borrow` | Ownership tracking: `BorrowState`, lifetime constraints |
| `verification` | Contracts, formulas, VC generation |
| `gradual` | Gradual typing with cast elaboration |
| `inference` | Type, effect, mode, and region inference |
| `encoding` | Binary and text serialization |
| `pipeline` | Compilation pipeline orchestration |

## License

Apache-2.0
