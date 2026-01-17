# Test Data for llm-tldr-rs

## Directory Structure

```
data/
├── projects/           # Real-world codebases (git submodules, shallow)
│   ├── python/         # flask, httpx
│   ├── typescript/     # deno_std
│   ├── rust/           # ripgrep
│   ├── go/             # gin
│   ├── java/           # guava
│   ├── c/              # redis
│   └── cpp/            # nlohmann/json
├── ffi/                # Cross-language binding examples (sparse checkout)
│   ├── pybind11/
│   ├── pyo3/
│   └── napi-rs/
├── bundles/            # Minified JS for bundle diff testing
│   ├── real/           # Downloaded from npm releases
│   └── synthetic/      # Controlled test cases with known diffs
├── security/           # Security pattern test cases
│   └── vulnerable/     # Crafted vulnerability patterns by language
├── synthetic/          # Hand-crafted edge cases
│   ├── edge-cases/     # Extreme patterns (deep nesting, huge functions)
│   └── patterns/       # Design pattern examples
├── monorepo/           # Generated large-scale test data
└── scripts/            # Data management scripts
```

## Setup

```bash
# Initialize all submodules (shallow clone)
./data/scripts/init.sh

# Or manually:
git submodule update --init --depth 1
```

## Submodules

| Path | Repository | Purpose |
|------|------------|---------|
| `projects/python/flask` | pallets/flask | Python parsing, git history, security |
| `projects/python/httpx` | encode/httpx | Async Python, type hints |
| `projects/typescript/deno_std` | denoland/deno_std | Clean TypeScript |
| `projects/rust/ripgrep` | BurntSushi/ripgrep | Rust, performance-critical |
| `projects/go/gin` | gin-gonic/gin | Go patterns |
| `projects/java/guava` | google/guava | Java, generics |
| `projects/c/redis` | redis/redis | C, event loop |
| `projects/cpp/json` | nlohmann/json | C++, templates |
| `ffi/pybind11` | pybind/pybind11 | Python-C++ bindings |
| `ffi/pyo3` | PyO3/pyo3 | Python-Rust bindings |
| `ffi/napi-rs` | napi-rs/napi-rs | Node-Rust bindings |
| `ffi/usearch` | unum-cloud/usearch | Multi-language bindings (C/C++/Py/Rust/JS/Java/Go/C#/Swift/WASM) |

## CI Tiers

### Tier 1: Always Run (~30MB, ~2min)
- `projects/python/flask/`
- `projects/rust/ripgrep/`
- `security/vulnerable/`
- `synthetic/edge-cases/`

### Tier 2: Weekly (~80MB, ~10min)
- `projects/typescript/deno_std/`
- `projects/go/gin/`
- `ffi/*/`
- `bundles/real/`

### Tier 3: Release Only (~200MB+, ~30min)
- `projects/java/guava/`
- `projects/c/redis/`
- `projects/cpp/json/`
- `monorepo/`

## Licenses

All submodules use permissive licenses (MIT, Apache-2.0, BSD):
- flask: BSD-3-Clause
- httpx: BSD-3-Clause
- deno_std: MIT
- ripgrep: MIT/Unlicense
- gin: MIT
- guava: Apache-2.0
- redis: BSD-3-Clause
- json: MIT
- pybind11: BSD-3-Clause
- pyo3: MIT/Apache-2.0
- napi-rs: MIT
- usearch: Apache-2.0
