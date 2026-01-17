#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DATA_DIR="$(dirname "$SCRIPT_DIR")"
ROOT_DIR="$(dirname "$DATA_DIR")"

cd "$ROOT_DIR"

echo "=== Initializing llm-tldr-rs test data ==="

# Check if .gitmodules exists in root (it should be moved there)
if [[ ! -f ".gitmodules" ]] && [[ -f "data/.gitmodules" ]]; then
    echo "Moving .gitmodules to repository root..."
    mv data/.gitmodules .gitmodules
fi

echo ""
echo "=== Initializing git submodules (shallow clone) ==="
git submodule update --init --depth 1 --jobs 4

echo ""
echo "=== Setting up sparse checkout for FFI repos ==="

# pybind11 - only tests and examples
if [[ -d "data/ffi/pybind11/.git" ]]; then
    cd data/ffi/pybind11
    git sparse-checkout init --cone 2>/dev/null || true
    git sparse-checkout set tests include/pybind11
    cd "$ROOT_DIR"
fi

# pyo3 - only examples
if [[ -d "data/ffi/pyo3/.git" ]]; then
    cd data/ffi/pyo3
    git sparse-checkout init --cone 2>/dev/null || true
    git sparse-checkout set examples guide/src
    cd "$ROOT_DIR"
fi

# napi-rs - only examples
if [[ -d "data/ffi/napi-rs/.git" ]]; then
    cd data/ffi/napi-rs
    git sparse-checkout init --cone 2>/dev/null || true
    git sparse-checkout set examples crates/napi/src
    cd "$ROOT_DIR"
fi

echo ""
echo "=== Summary ==="
echo "Total size:"
du -sh data/

echo ""
echo "Submodule status:"
git submodule status

echo ""
echo "=== Done ==="
