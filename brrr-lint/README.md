# brrr-lint

A fast linter and language server for [F*](https://fstar-lang.org/) (FStar), the proof-oriented programming language.

## Installation

```bash
cargo install brrr-lint
```

## Usage

```bash
# Check F* files for issues
brrr-lint check src/

# Preview fixes (dry-run mode - default)
brrr-lint fix src/

# Apply fixes
brrr-lint fix src/ --apply

# Run as LSP server
brrr-lint serve

# List all rules
brrr-lint rules
```

## Rules

| Code | Description |
|------|-------------|
| FST001 | Duplicate type definitions across .fst/.fsti |
| FST002 | Interface/implementation mismatches |
| FST003 | Interface declaration ordering |
| FST004 | Unused module opens |
| FST005 | Dead code detection |
| FST006 | Naming convention violations |
| FST007 | Large match expressions |
| FST008 | Broad imports |
| FST009 | Module dependency issues |
| FST010 | Proof hint suggestions |
| FST011 | Effect issues (admit/assume) |
| FST012 | Refinement type simplification |
| FST013 | Missing documentation |
| FST014 | Test suggestions |
| FST015 | Security patterns |
| FST016 | Verification performance |
| FST017 | Z3 complexity analysis |

## Safety

By default, `brrr-lint fix` runs in **dry-run mode** and shows what would be changed without modifying files. Use `--apply` to write changes.

Fix safety levels:
- **Safe**: Auto-applied with `--apply`
- **Caution**: Applied with warning
- **Unsafe**: Requires `--force --apply`

## License

Apache-2.0
