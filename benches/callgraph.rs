//! Comprehensive benchmarks for call graph analysis.
//!
//! Measures performance of:
//! - Call extraction from source files
//! - Call graph construction
//! - Graph queries (impact analysis, dead code detection)
//! - Per-language method resolution
//! - Import resolution

use std::fs;
use std::io::Write;
use std::path::PathBuf;

use criterion::{black_box, criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use tempfile::TempDir;

use go_brrr::callgraph::indexer::FunctionIndex;
use go_brrr::callgraph::types::{CallEdge, CallGraph, FunctionRef};
use go_brrr::callgraph::{analyze_dead_code, analyze_impact, build, DeadCodeConfig, ImpactConfig};

// =============================================================================
// Test Data Generation
// =============================================================================

/// Generates a Python file with a specified number of functions and call patterns.
fn generate_python_file_with_calls(
    num_functions: usize,
    calls_per_function: usize,
    with_classes: bool,
) -> String {
    let mut content = String::with_capacity(num_functions * 200);

    // Add some imports
    content.push_str("import os\nimport sys\nfrom typing import List, Dict\n\n");

    if with_classes {
        // Generate class with methods
        content.push_str("class DataProcessor:\n");
        content.push_str("    def __init__(self, config: Dict):\n");
        content.push_str("        self.config = config\n\n");

        for i in 0..num_functions / 2 {
            content.push_str(&format!("    def method_{i}(self, data):\n"));
            content.push_str(&format!("        \"\"\"Process data variant {i}.\"\"\"\n"));

            // Add method calls
            for j in 0..calls_per_function {
                let target = (i + j + 1) % (num_functions / 2);
                content.push_str(&format!("        self.method_{target}(data)\n"));
            }
            content.push_str("        return data\n\n");
        }
        content.push_str("\n");
    }

    // Generate standalone functions
    for i in 0..num_functions {
        content.push_str(&format!("def process_item_{i}(item):\n"));
        content.push_str(&format!("    \"\"\"Process item variant {i}.\"\"\"\n"));

        // Add function calls
        for j in 0..calls_per_function {
            let target = (i + j + 1) % num_functions;
            content.push_str(&format!("    result = process_item_{target}(item)\n"));
        }

        // Add some method chain calls
        if i % 3 == 0 {
            content.push_str("    items = []\n");
            content.push_str("    items.append(item)\n");
            content.push_str("    filtered = list(filter(lambda x: x, items))\n");
            content.push_str("    mapped = list(map(lambda x: x * 2, filtered))\n");
        }

        content.push_str("    return result\n\n");
    }

    // Add main entry point
    content.push_str("def main():\n");
    content.push_str("    process_item_0(None)\n");
    if with_classes {
        content.push_str("    processor = DataProcessor({})\n");
        content.push_str("    processor.method_0(None)\n");
    }
    content.push_str("\n\nif __name__ == '__main__':\n    main()\n");

    content
}

/// Generates a TypeScript file with various call patterns.
fn generate_typescript_file_with_calls(num_functions: usize, calls_per_function: usize) -> String {
    let mut content = String::with_capacity(num_functions * 250);

    content.push_str("import { EventEmitter } from 'events';\n\n");

    // Generate a class with methods
    content.push_str("export class ServiceHandler extends EventEmitter {\n");
    content.push_str("    private data: Map<string, any> = new Map();\n\n");

    for i in 0..num_functions / 3 {
        content.push_str(&format!("    public async handleRequest{i}(req: any): Promise<any> {{\n"));
        content.push_str(&format!("        // Handle request variant {i}\n"));

        // Add this.method() calls
        for j in 0..calls_per_function {
            let target = (i + j + 1) % (num_functions / 3);
            content.push_str(&format!("        await this.handleRequest{target}(req);\n"));
        }

        content.push_str("        return this.data.get(req.id);\n");
        content.push_str("    }\n\n");
    }

    content.push_str("}\n\n");

    // Generate arrow functions
    for i in 0..num_functions / 3 {
        content.push_str(&format!(
            "export const processData{i} = async (data: any[]): Promise<any[]> => {{\n"
        ));

        // Add chained method calls
        content.push_str("    return data\n");
        content.push_str("        .filter(x => x !== null)\n");
        content.push_str("        .map(x => x * 2)\n");
        content.push_str("        .reduce((a, b) => a + b, 0);\n");
        content.push_str("};\n\n");
    }

    // Generate regular functions
    for i in 0..num_functions / 3 {
        content.push_str(&format!("export function transform{i}(input: any): any {{\n"));

        for j in 0..calls_per_function {
            let target = (i + j + 1) % (num_functions / 3);
            content.push_str(&format!("    const result{j} = transform{target}(input);\n"));
        }

        content.push_str("    return input;\n");
        content.push_str("}\n\n");
    }

    content
}

/// Generates a Rust file with impl blocks and method calls.
fn generate_rust_file_with_calls(num_functions: usize, calls_per_function: usize) -> String {
    let mut content = String::with_capacity(num_functions * 200);

    content.push_str("use std::collections::HashMap;\n\n");

    // Generate struct and impl
    content.push_str("#[derive(Debug, Default)]\n");
    content.push_str("pub struct Processor {\n");
    content.push_str("    data: HashMap<String, i64>,\n");
    content.push_str("}\n\n");

    content.push_str("impl Processor {\n");

    for i in 0..num_functions / 2 {
        content.push_str(&format!("    pub fn process_{i}(&mut self, input: i64) -> i64 {{\n"));

        for j in 0..calls_per_function {
            let target = (i + j + 1) % (num_functions / 2);
            content.push_str(&format!("        let _r{j} = self.process_{target}(input);\n"));
        }

        content.push_str("        input * 2\n");
        content.push_str("    }\n\n");
    }

    content.push_str("}\n\n");

    // Generate free functions
    for i in 0..num_functions / 2 {
        content.push_str(&format!("pub fn compute_{i}(value: i64) -> i64 {{\n"));

        for j in 0..calls_per_function {
            let target = (i + j + 1) % (num_functions / 2);
            content.push_str(&format!("    let _r{j} = compute_{target}(value);\n"));
        }

        content.push_str("    value + 1\n");
        content.push_str("}\n\n");
    }

    // Main function
    content.push_str("fn main() {\n");
    content.push_str("    let mut p = Processor::default();\n");
    content.push_str("    p.process_0(42);\n");
    content.push_str("    compute_0(100);\n");
    content.push_str("}\n");

    content
}

/// Generates a Go file with receiver methods.
fn generate_go_file_with_calls(num_functions: usize, calls_per_function: usize) -> String {
    let mut content = String::with_capacity(num_functions * 200);

    content.push_str("package main\n\n");
    content.push_str("import \"fmt\"\n\n");

    // Generate struct and receiver methods
    content.push_str("type Handler struct {\n");
    content.push_str("\tdata map[string]int\n");
    content.push_str("}\n\n");

    for i in 0..num_functions / 2 {
        content.push_str(&format!("func (h *Handler) Process{i}(input int) int {{\n"));

        for j in 0..calls_per_function {
            let target = (i + j + 1) % (num_functions / 2);
            content.push_str(&format!("\t_ = h.Process{target}(input)\n"));
        }

        content.push_str("\treturn input * 2\n");
        content.push_str("}\n\n");
    }

    // Generate package functions
    for i in 0..num_functions / 2 {
        content.push_str(&format!("func Calculate{i}(value int) int {{\n"));

        for j in 0..calls_per_function {
            let target = (i + j + 1) % (num_functions / 2);
            content.push_str(&format!("\t_ = Calculate{target}(value)\n"));
        }

        content.push_str("\treturn value + 1\n");
        content.push_str("}\n\n");
    }

    content.push_str("func main() {\n");
    content.push_str("\th := &Handler{data: make(map[string]int)}\n");
    content.push_str("\tfmt.Println(h.Process0(42))\n");
    content.push_str("\tfmt.Println(Calculate0(100))\n");
    content.push_str("}\n");

    content
}

/// Generates a Java file with static and instance methods.
fn generate_java_file_with_calls(num_functions: usize, calls_per_function: usize) -> String {
    let mut content = String::with_capacity(num_functions * 250);

    content.push_str("package com.example;\n\n");
    content.push_str("import java.util.*;\n");
    content.push_str("import java.util.stream.*;\n\n");

    content.push_str("public class DataService {\n\n");

    // Instance methods
    for i in 0..num_functions / 3 {
        content.push_str(&format!("    public int processItem{i}(int input) {{\n"));

        for j in 0..calls_per_function {
            let target = (i + j + 1) % (num_functions / 3);
            content.push_str(&format!("        int r{j} = this.processItem{target}(input);\n"));
        }

        content.push_str("        return input * 2;\n");
        content.push_str("    }\n\n");
    }

    // Static methods
    for i in 0..num_functions / 3 {
        content.push_str(&format!("    public static int compute{i}(int value) {{\n"));

        for j in 0..calls_per_function {
            let target = (i + j + 1) % (num_functions / 3);
            content.push_str(&format!("        int r{j} = DataService.compute{target}(value);\n"));
        }

        content.push_str("        return value + 1;\n");
        content.push_str("    }\n\n");
    }

    // Methods with lambdas
    for i in 0..num_functions / 3 {
        content.push_str(&format!(
            "    public List<Integer> transform{i}(List<Integer> items) {{\n"
        ));
        content.push_str("        return items.stream()\n");
        content.push_str("            .filter(x -> x != null)\n");
        content.push_str("            .map(x -> x * 2)\n");
        content.push_str("            .collect(Collectors.toList());\n");
        content.push_str("    }\n\n");
    }

    content.push_str("    public static void main(String[] args) {\n");
    content.push_str("        DataService service = new DataService();\n");
    content.push_str("        service.processItem0(42);\n");
    content.push_str("        DataService.compute0(100);\n");
    content.push_str("    }\n");
    content.push_str("}\n");

    content
}

/// Creates a temporary project with multiple source files.
fn create_test_project(num_files: usize, functions_per_file: usize, lang: &str) -> TempDir {
    let dir = TempDir::new().expect("Failed to create temp dir");

    for i in 0..num_files {
        let (filename, content) = match lang {
            "python" => (
                format!("module_{i}.py"),
                generate_python_file_with_calls(functions_per_file, 2, i % 3 == 0),
            ),
            "typescript" => (
                format!("service_{i}.ts"),
                generate_typescript_file_with_calls(functions_per_file, 2),
            ),
            "rust" => (
                format!("lib_{i}.rs"),
                generate_rust_file_with_calls(functions_per_file, 2),
            ),
            "go" => (
                format!("handler_{i}.go"),
                generate_go_file_with_calls(functions_per_file, 2),
            ),
            "java" => (
                format!("Service{i}.java"),
                generate_java_file_with_calls(functions_per_file, 2),
            ),
            _ => continue,
        };

        let path = dir.path().join(&filename);
        let mut file = fs::File::create(&path).expect("Failed to create file");
        file.write_all(content.as_bytes())
            .expect("Failed to write content");
    }

    dir
}

/// Creates a synthetic call graph for query benchmarks.
fn create_synthetic_call_graph(num_functions: usize, edges_per_function: usize) -> CallGraph {
    let mut graph = CallGraph::default();

    // Create function refs
    let functions: Vec<FunctionRef> = (0..num_functions)
        .map(|i| FunctionRef {
            file: format!("file_{}.py", i / 10),
            name: format!("func_{i}"),
            qualified_name: Some(format!("module.func_{i}")),
        })
        .collect();

    // Create edges (each function calls edges_per_function others)
    for (i, caller) in functions.iter().enumerate() {
        for j in 0..edges_per_function {
            let callee_idx = (i + j + 1) % num_functions;
            graph.edges.push(CallEdge {
                caller: caller.clone(),
                callee: functions[callee_idx].clone(),
                call_line: (j + 1) * 10,
            });
        }
    }

    // Add some entry points
    for i in [0, num_functions / 4, num_functions / 2, 3 * num_functions / 4] {
        if i < num_functions {
            graph.edges.push(CallEdge {
                caller: FunctionRef {
                    file: "main.py".to_string(),
                    name: "main".to_string(),
                    qualified_name: Some("main.main".to_string()),
                },
                callee: functions[i].clone(),
                call_line: i,
            });
        }
    }

    graph.build_indexes();
    graph
}

/// Creates a deep call chain for transitive closure benchmarks.
fn create_deep_call_chain(depth: usize, branches_per_level: usize) -> CallGraph {
    let mut graph = CallGraph::default();
    let mut queue: Vec<(FunctionRef, usize)> = Vec::new();

    // Root function
    let root = FunctionRef {
        file: "main.py".to_string(),
        name: "main".to_string(),
        qualified_name: Some("main.main".to_string()),
    };

    queue.push((root, 0));
    let mut func_counter = 0;

    while let Some((caller, level)) = queue.pop() {
        if level >= depth {
            continue;
        }

        for b in 0..branches_per_level {
            func_counter += 1;
            let callee = FunctionRef {
                file: format!("module_{}.py", level),
                name: format!("func_{}_{}", level, func_counter),
                qualified_name: Some(format!("module_{}.func_{}_{}", level, level, func_counter)),
            };

            graph.edges.push(CallEdge {
                caller: caller.clone(),
                callee: callee.clone(),
                call_line: b * 5 + 10,
            });

            queue.push((callee, level + 1));
        }
    }

    graph.build_indexes();
    graph
}

// =============================================================================
// Call Extraction Benchmarks
// =============================================================================

fn bench_call_extraction(c: &mut Criterion) {
    let mut group = c.benchmark_group("call_extraction");

    // Single function with few calls
    let simple_python = r#"
def process(data):
    validate(data)
    transform(data)
    return save(data)
"#;

    // File with many functions
    let many_funcs = generate_python_file_with_calls(50, 3, true);

    // Method chains
    let method_chains = r#"
def process_pipeline(data):
    result = data.strip().lower().split(',')
    filtered = list(filter(lambda x: len(x) > 0, result))
    mapped = list(map(lambda x: x.upper(), filtered))
    return sorted(mapped, key=lambda x: len(x))
"#;

    // Closures and lambdas
    let closures = r#"
def higher_order():
    callbacks = []

    def callback1(x):
        return x * 2

    def callback2(x):
        return x + 1

    callbacks.append(callback1)
    callbacks.append(callback2)

    process = lambda items: list(map(lambda f: f(42), callbacks))
    result = process([1, 2, 3])

    nested = lambda x: (lambda y: y * x)(10)
    return result
"#;

    group.bench_function("single_function", |b| {
        let dir = TempDir::new().unwrap();
        let path = dir.path().join("simple.py");
        fs::write(&path, simple_python).unwrap();

        b.iter(|| {
            let result = build(black_box(dir.path().to_str().unwrap()));
            black_box(result)
        });
    });

    group.bench_function("many_functions_50", |b| {
        let dir = TempDir::new().unwrap();
        let path = dir.path().join("many.py");
        fs::write(&path, &many_funcs).unwrap();

        b.iter(|| {
            let result = build(black_box(dir.path().to_str().unwrap()));
            black_box(result)
        });
    });

    group.bench_function("method_chains", |b| {
        let dir = TempDir::new().unwrap();
        let path = dir.path().join("chains.py");
        fs::write(&path, method_chains).unwrap();

        b.iter(|| {
            let result = build(black_box(dir.path().to_str().unwrap()));
            black_box(result)
        });
    });

    group.bench_function("closures_and_lambdas", |b| {
        let dir = TempDir::new().unwrap();
        let path = dir.path().join("closures.py");
        fs::write(&path, closures).unwrap();

        b.iter(|| {
            let result = build(black_box(dir.path().to_str().unwrap()));
            black_box(result)
        });
    });

    group.finish();
}

// =============================================================================
// Call Graph Building Benchmarks
// =============================================================================

fn bench_call_graph_building(c: &mut Criterion) {
    let mut group = c.benchmark_group("callgraph_building");
    group.sample_size(20); // Reduce sample size for slower benchmarks

    // Small project (10 files)
    group.bench_function("small_project_10_files", |b| {
        b.iter_batched(
            || create_test_project(10, 10, "python"),
            |dir| {
                let result = build(black_box(dir.path().to_str().unwrap()));
                black_box(result)
            },
            BatchSize::SmallInput,
        );
    });

    // Medium project (50 files)
    group.bench_function("medium_project_50_files", |b| {
        b.iter_batched(
            || create_test_project(50, 15, "python"),
            |dir| {
                let result = build(black_box(dir.path().to_str().unwrap()));
                black_box(result)
            },
            BatchSize::SmallInput,
        );
    });

    // Build index only (pre-step)
    group.bench_function("build_function_index_50_files", |b| {
        let dir = create_test_project(50, 15, "python");
        let files: Vec<PathBuf> = fs::read_dir(dir.path())
            .unwrap()
            .filter_map(|e| e.ok())
            .map(|e| e.path())
            .collect();

        b.iter(|| {
            let result = FunctionIndex::build(black_box(&files));
            black_box(result)
        });
    });

    // Build indexes on pre-constructed graph
    group.bench_function("build_graph_indexes_1000_edges", |b| {
        b.iter_batched(
            || {
                let mut graph = create_synthetic_call_graph(200, 5);
                graph.callers.clear();
                graph.callees.clear();
                graph
            },
            |mut graph| {
                graph.build_indexes();
                black_box(graph)
            },
            BatchSize::SmallInput,
        );
    });

    group.finish();
}

// =============================================================================
// Call Graph Query Benchmarks
// =============================================================================

fn bench_call_graph_queries(c: &mut Criterion) {
    let mut group = c.benchmark_group("callgraph_queries");

    // Impact analysis benchmarks
    let graph_small = create_synthetic_call_graph(100, 3);
    let graph_medium = create_synthetic_call_graph(500, 4);
    let graph_deep = create_deep_call_chain(10, 3);

    // Find all callers (impact analysis)
    group.bench_function("impact_analysis_100_nodes_depth_3", |b| {
        let graph = graph_small.clone();
        b.iter(|| {
            let config = ImpactConfig::new().with_depth(3);
            let result = analyze_impact(black_box(&graph), black_box("func_50"), config);
            black_box(result)
        });
    });

    group.bench_function("impact_analysis_500_nodes_depth_5", |b| {
        let graph = graph_medium.clone();
        b.iter(|| {
            let config = ImpactConfig::new().with_depth(5);
            let result = analyze_impact(black_box(&graph), black_box("func_250"), config);
            black_box(result)
        });
    });

    group.bench_function("impact_analysis_unlimited_depth", |b| {
        let graph = graph_medium.clone();
        b.iter(|| {
            let config = ImpactConfig::new().with_depth(0); // unlimited
            let result = analyze_impact(black_box(&graph), black_box("func_250"), config);
            black_box(result)
        });
    });

    // Find all callees
    group.bench_function("find_callees_100_nodes", |b| {
        let graph = graph_small.clone();
        let target = FunctionRef {
            file: String::new(),
            name: "func_0".to_string(),
            qualified_name: None,
        };

        b.iter(|| {
            let result = graph.get_callees(black_box(&target), black_box(5));
            black_box(result)
        });
    });

    group.bench_function("find_callees_500_nodes", |b| {
        let graph = graph_medium.clone();
        let target = FunctionRef {
            file: String::new(),
            name: "func_0".to_string(),
            qualified_name: None,
        };

        b.iter(|| {
            let result = graph.get_callees(black_box(&target), black_box(10));
            black_box(result)
        });
    });

    // Dead code detection
    group.bench_function("dead_code_100_nodes", |b| {
        let graph = graph_small.clone();
        b.iter(|| {
            let result = analyze_dead_code(black_box(&graph));
            black_box(result)
        });
    });

    group.bench_function("dead_code_500_nodes", |b| {
        let graph = graph_medium.clone();
        b.iter(|| {
            let result = analyze_dead_code(black_box(&graph));
            black_box(result)
        });
    });

    group.bench_function("dead_code_with_config", |b| {
        let graph = graph_medium.clone();
        let config = DeadCodeConfig {
            min_confidence: 0.8,
            extra_entry_patterns: vec!["api_".to_string(), "handle_".to_string()],
            filter_patterns: vec!["callback".to_string()],
            language: Some("python".to_string()),
            include_public_api_patterns: false,
        };

        b.iter(|| {
            let result =
                go_brrr::callgraph::dead::analyze_dead_code_with_config(black_box(&graph), &config);
            black_box(result)
        });
    });

    // Transitive closure (deep graph)
    group.bench_function("transitive_closure_depth_10", |b| {
        let graph = graph_deep.clone();
        let target = FunctionRef {
            file: String::new(),
            name: "main".to_string(),
            qualified_name: None,
        };

        b.iter(|| {
            let result = graph.get_callees(black_box(&target), black_box(15));
            black_box(result)
        });
    });

    group.finish();
}

// =============================================================================
// Per-Language Call Resolution Benchmarks
// =============================================================================

fn bench_language_resolution(c: &mut Criterion) {
    let mut group = c.benchmark_group("language_resolution");
    group.sample_size(20);

    // Python self.method() resolution
    group.bench_function("python_self_method", |b| {
        b.iter_batched(
            || create_test_project(5, 20, "python"),
            |dir| {
                let result = build(black_box(dir.path().to_str().unwrap()));
                black_box(result)
            },
            BatchSize::SmallInput,
        );
    });

    // TypeScript this.method() resolution
    group.bench_function("typescript_this_method", |b| {
        b.iter_batched(
            || create_test_project(5, 20, "typescript"),
            |dir| {
                let result = build(black_box(dir.path().to_str().unwrap()));
                black_box(result)
            },
            BatchSize::SmallInput,
        );
    });

    // Rust impl method resolution
    group.bench_function("rust_impl_method", |b| {
        b.iter_batched(
            || create_test_project(5, 20, "rust"),
            |dir| {
                let result = build(black_box(dir.path().to_str().unwrap()));
                black_box(result)
            },
            BatchSize::SmallInput,
        );
    });

    // Go receiver method resolution
    group.bench_function("go_receiver_method", |b| {
        b.iter_batched(
            || create_test_project(5, 20, "go"),
            |dir| {
                let result = build(black_box(dir.path().to_str().unwrap()));
                black_box(result)
            },
            BatchSize::SmallInput,
        );
    });

    // Java static vs instance method resolution
    group.bench_function("java_method_resolution", |b| {
        b.iter_batched(
            || create_test_project(5, 20, "java"),
            |dir| {
                let result = build(black_box(dir.path().to_str().unwrap()));
                black_box(result)
            },
            BatchSize::SmallInput,
        );
    });

    group.finish();
}

// =============================================================================
// Import Resolution Benchmarks
// =============================================================================

fn bench_import_resolution(c: &mut Criterion) {
    let mut group = c.benchmark_group("import_resolution");
    group.sample_size(20);

    // Python imports with various patterns
    let python_imports = r#"
# Standard library imports
import os
import sys
from pathlib import Path
from typing import List, Dict, Optional, Union
from collections import defaultdict, Counter
from functools import lru_cache, partial

# Relative imports
from . import utils
from .helpers import process_data, validate_input
from ..core import base_handler
from ...common.utils import logger

# Aliased imports
import numpy as np
import pandas as pd
from sklearn.model_selection import train_test_split as tts

# Star imports (should be detected)
from config import *

def main():
    data = pd.DataFrame()
    result = process_data(data)
    logger.info(result)
    cache = lru_cache(maxsize=100)
    path = Path("./data")
    return os.path.exists(path)
"#;

    // TypeScript imports
    let typescript_imports = r#"
// Named imports
import { EventEmitter } from 'events';
import { readFile, writeFile } from 'fs/promises';
import { join, resolve } from 'path';

// Default imports
import express from 'express';
import React from 'react';

// Namespace imports
import * as utils from './utils';
import * as config from '../config';

// Side effect imports
import './styles.css';
import 'reflect-metadata';

// Type imports
import type { Config, Handler } from './types';

// Re-exports
export { default as Logger } from './logger';
export * from './helpers';

async function main(): Promise<void> {
    const app = express();
    const emitter = new EventEmitter();
    const data = await readFile(join(__dirname, 'data.json'));
    utils.process(data);
}
"#;

    // Cross-file references (multi-module project)
    group.bench_function("python_imports_complex", |b| {
        let dir = TempDir::new().unwrap();
        fs::write(dir.path().join("main.py"), python_imports).unwrap();
        fs::write(dir.path().join("utils.py"), "def process_data(x): return x").unwrap();
        fs::write(
            dir.path().join("helpers.py"),
            "def process_data(x): pass\ndef validate_input(x): pass",
        )
        .unwrap();

        b.iter(|| {
            let result = build(black_box(dir.path().to_str().unwrap()));
            black_box(result)
        });
    });

    group.bench_function("typescript_imports_complex", |b| {
        let dir = TempDir::new().unwrap();
        fs::write(dir.path().join("main.ts"), typescript_imports).unwrap();
        fs::write(
            dir.path().join("utils.ts"),
            "export function process(x: any): any { return x; }",
        )
        .unwrap();

        b.iter(|| {
            let result = build(black_box(dir.path().to_str().unwrap()));
            black_box(result)
        });
    });

    // Re-exports resolution
    let reexport_index = r#"
# Re-export pattern
from .module_a import ClassA, func_a
from .module_b import ClassB, func_b
from .module_c import *

__all__ = ['ClassA', 'ClassB', 'func_a', 'func_b']
"#;

    group.bench_function("python_reexports", |b| {
        let dir = TempDir::new().unwrap();
        fs::write(dir.path().join("__init__.py"), reexport_index).unwrap();
        fs::write(dir.path().join("module_a.py"), "class ClassA: pass\ndef func_a(): pass").unwrap();
        fs::write(dir.path().join("module_b.py"), "class ClassB: pass\ndef func_b(): pass").unwrap();
        fs::write(dir.path().join("module_c.py"), "class ClassC: pass\ndef func_c(): pass").unwrap();
        fs::write(
            dir.path().join("consumer.py"),
            "from . import ClassA, func_a\ndef use(): return ClassA()",
        )
        .unwrap();

        b.iter(|| {
            let result = build(black_box(dir.path().to_str().unwrap()));
            black_box(result)
        });
    });

    group.finish();
}

// =============================================================================
// Memory Usage Benchmarks
// =============================================================================

fn bench_memory_patterns(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_patterns");
    group.sample_size(10);

    // Large graph memory pattern
    for size in [100, 500, 1000] {
        group.bench_with_input(
            BenchmarkId::new("graph_construction", size),
            &size,
            |b, &size| {
                b.iter(|| {
                    let graph = create_synthetic_call_graph(size, 4);
                    black_box(graph)
                });
            },
        );
    }

    // Index memory pattern
    for files in [10, 50, 100] {
        group.bench_with_input(
            BenchmarkId::new("index_construction", files),
            &files,
            |b, &files| {
                b.iter_batched(
                    || create_test_project(files, 10, "python"),
                    |dir| {
                        let files: Vec<PathBuf> = fs::read_dir(dir.path())
                            .unwrap()
                            .filter_map(|e| e.ok())
                            .map(|e| e.path())
                            .collect();
                        let index = FunctionIndex::build(&files);
                        black_box(index)
                    },
                    BatchSize::SmallInput,
                );
            },
        );
    }

    group.finish();
}

// =============================================================================
// Criterion Groups
// =============================================================================

criterion_group!(
    benches,
    bench_call_extraction,
    bench_call_graph_building,
    bench_call_graph_queries,
    bench_language_resolution,
    bench_import_resolution,
    bench_memory_patterns,
);

criterion_main!(benches);
