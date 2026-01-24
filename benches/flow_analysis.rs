//! Comprehensive benchmarks for CFG (Control Flow Graph) and DFG (Data Flow Graph) analysis.
//!
//! These benchmarks measure the performance of flow analysis across:
//! - Different control flow constructs (branches, loops, exceptions)
//! - Different data flow patterns (assignments, mutations, closures)
//! - Different programming languages (Python, TypeScript, Rust, Go, Java)
//! - Different function sizes (10, 100, 1000 statements)

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use go_brrr::cfg::CfgBuilder;
use go_brrr::dfg::DfgBuilder;

// =============================================================================
// Test Code Generators
// =============================================================================

/// Generate Python code with a simple linear function (no branches).
fn python_linear_function(statements: usize) -> String {
    let mut code = String::from("def linear_func(x):\n");
    for i in 0..statements {
        code.push_str(&format!("    v{} = x + {}\n", i, i));
    }
    code.push_str(&format!("    return v{}\n", statements.saturating_sub(1)));
    code
}

/// Generate Python code with if/else branches.
fn python_branching_function() -> &'static str {
    r#"
def branching_func(x, y, z):
    if x > 0:
        result = x * 2
    elif x < 0:
        result = x * -1
    else:
        result = 0

    if y > 0:
        result = result + y
    else:
        result = result - y

    if z != 0:
        result = result / z

    return result
"#
}

/// Generate Python code with various loop constructs.
fn python_loop_function() -> &'static str {
    r#"
def loop_func(items, n):
    total = 0

    for item in items:
        total += item

    i = 0
    while i < n:
        total += i
        i += 1

    for j in range(10):
        for k in range(5):
            total += j * k

    return total
"#
}

/// Generate Python code with nested control flow.
fn python_nested_control_flow() -> &'static str {
    r#"
def nested_func(data, threshold, limit):
    result = 0
    count = 0

    for item in data:
        if item > threshold:
            if count < limit:
                result += item * 2
                count += 1
            else:
                break
        elif item < 0:
            continue
        else:
            for i in range(item):
                if i % 2 == 0:
                    result += i
                else:
                    result -= i

    return result
"#
}

/// Generate Python code with try/except/finally.
fn python_exception_handling() -> &'static str {
    r#"
def exception_func(a, b, c):
    result = 0

    try:
        result = a / b
        try:
            result = result + c
        except TypeError:
            result = 0
    except ZeroDivisionError as e:
        result = -1
    except Exception as e:
        result = -2
    finally:
        result = result + 1

    return result
"#
}

/// Generate Python code with match/case statements (Python 3.10+).
fn python_match_statement() -> &'static str {
    r#"
def match_func(command, value):
    result = 0

    match command:
        case "add":
            result = value + 10
        case "subtract":
            result = value - 10
        case "multiply":
            result = value * 2
        case "divide" if value != 0:
            result = value // 2
        case _:
            result = value

    return result
"#
}

/// Generate Python code with all control structures combined.
fn python_complex_function() -> &'static str {
    r#"
def complex_func(data, config, options):
    result = 0
    processed = 0
    errors = []

    if not data:
        return result

    for item in data:
        try:
            if item.get("type") == "number":
                value = item.get("value", 0)
                if value > config.get("threshold", 0):
                    for i in range(value):
                        if i % 2 == 0:
                            result += i
                        else:
                            result -= i
                elif value < 0:
                    continue
                else:
                    result += value
            elif item.get("type") == "string":
                match item.get("action"):
                    case "upper":
                        result += 1
                    case "lower":
                        result -= 1
                    case _:
                        pass
            else:
                while processed < options.get("limit", 10):
                    result += 1
                    processed += 1
                    if processed > 5:
                        break
        except KeyError as e:
            errors.append(str(e))
        except Exception as e:
            errors.append(str(e))
            if len(errors) > 10:
                break
        finally:
            processed += 1

    return result
"#
}

/// Generate TypeScript code with optional chaining and nullish coalescing.
fn typescript_optional_chaining() -> &'static str {
    r#"
function optionalFunc(user: any, config: any): number {
    const name = user?.profile?.name ?? "default";
    const age = user?.age ?? 0;
    const settings = config?.settings?.theme ?? "light";

    let result = 0;

    if (user?.isActive) {
        result += age;
        if (user?.permissions?.canEdit) {
            result += 10;
        }
    }

    const items = user?.items ?? [];
    for (const item of items) {
        result += item?.value ?? 0;
    }

    return result;
}
"#
}

/// Generate Rust code with ? operator and match.
fn rust_error_handling() -> &'static str {
    r#"
fn rust_func(input: Option<i32>, data: Result<Vec<i32>, String>) -> Result<i32, String> {
    let value = input.ok_or("No input")?;
    let items = data?;

    let mut result = 0;

    match value {
        0 => result = 0,
        1..=10 => result = value * 2,
        11..=100 => {
            for item in items.iter() {
                result += item;
            }
        }
        _ => result = -1,
    }

    if let Some(first) = items.first() {
        result += first;
    }

    Ok(result)
}
"#
}

/// Generate Go code with goroutines and defer.
fn go_concurrency() -> &'static str {
    r#"
func goFunc(items []int, ch chan int) int {
    defer close(ch)

    result := 0

    for _, item := range items {
        if item > 0 {
            result += item
        } else if item < 0 {
            continue
        } else {
            break
        }
    }

    for i := 0; i < 10; i++ {
        result += i
    }

    switch result {
    case 0:
        result = 1
    case 1:
        result = 2
    default:
        result = result * 2
    }

    return result
}
"#
}

/// Generate Java code with try-with-resources.
fn java_try_with_resources() -> &'static str {
    r#"
public int javaFunc(String path, int limit) {
    int result = 0;

    try {
        result = Integer.parseInt(path);
    } catch (NumberFormatException e) {
        result = -1;
    } catch (Exception e) {
        result = -2;
    } finally {
        result += 1;
    }

    for (int i = 0; i < limit; i++) {
        if (i % 2 == 0) {
            result += i;
        } else {
            result -= i;
        }
    }

    switch (result) {
        case 0:
            result = 1;
            break;
        case 1:
            result = 2;
            break;
        default:
            result = result * 2;
    }

    return result;
}
"#
}

// =============================================================================
// DFG Test Code Generators
// =============================================================================

/// Generate Python code with simple variable assignments.
fn python_simple_assignments() -> &'static str {
    r#"
def assign_func(x, y, z):
    a = x
    b = y
    c = z
    d = a + b
    e = c * d
    f = e - a
    return f
"#
}

/// Generate Python code with many variable definitions.
fn python_many_variables(count: usize) -> String {
    let mut code = String::from("def many_vars_func(x):\n");
    for i in 0..count {
        if i == 0 {
            code.push_str(&format!("    v{} = x\n", i));
        } else {
            code.push_str(&format!("    v{} = v{} + 1\n", i, i - 1));
        }
    }
    code.push_str(&format!("    return v{}\n", count.saturating_sub(1)));
    code
}

/// Generate Python code with closures/lambdas.
fn python_closures() -> &'static str {
    r#"
def closure_func(items, multiplier):
    result = []

    transform = lambda x: x * multiplier

    for item in items:
        result.append(transform(item))

    squared = [x * x for x in result]
    filtered = [x for x in squared if x > 0]

    total = sum(filtered)

    return total
"#
}

/// Generate Python code with pattern matching data flow.
fn python_pattern_matching_dfg() -> &'static str {
    r#"
def pattern_func(data):
    result = 0

    match data:
        case {"type": "number", "value": v}:
            result = v * 2
        case {"type": "string", "value": s}:
            result = len(s)
        case [first, *rest]:
            result = first + sum(rest)
        case _:
            result = -1

    return result
"#
}

/// Generate Python code with complex mutations.
fn python_mutations() -> &'static str {
    r#"
def mutation_func(items):
    total = 0
    count = 0
    running_sum = 0

    for item in items:
        total += item
        count += 1
        running_sum = running_sum + item

        if count > 10:
            total -= 1
            count = 0

    average = total / count if count > 0 else 0

    result = {
        "total": total,
        "count": count,
        "average": average,
        "running_sum": running_sum
    }

    return result
"#
}

// =============================================================================
// CFG Benchmarks
// =============================================================================

fn bench_cfg_linear(c: &mut Criterion) {
    let mut group = c.benchmark_group("cfg_linear");

    let source = python_linear_function(10);
    group.throughput(Throughput::Elements(10));
    group.bench_function("python_10_statements", |b| {
        b.iter(|| {
            black_box(CfgBuilder::extract_from_source(
                black_box(&source),
                "python",
                "linear_func",
            ))
        })
    });

    group.finish();
}

fn bench_cfg_branching(c: &mut Criterion) {
    let mut group = c.benchmark_group("cfg_branching");

    let source = python_branching_function();
    group.bench_function("python_if_else", |b| {
        b.iter(|| {
            black_box(CfgBuilder::extract_from_source(
                black_box(source),
                "python",
                "branching_func",
            ))
        })
    });

    group.finish();
}

fn bench_cfg_loops(c: &mut Criterion) {
    let mut group = c.benchmark_group("cfg_loops");

    let source = python_loop_function();
    group.bench_function("python_for_while_nested", |b| {
        b.iter(|| {
            black_box(CfgBuilder::extract_from_source(
                black_box(source),
                "python",
                "loop_func",
            ))
        })
    });

    group.finish();
}

fn bench_cfg_nested(c: &mut Criterion) {
    let mut group = c.benchmark_group("cfg_nested");

    let source = python_nested_control_flow();
    group.bench_function("python_nested_control_flow", |b| {
        b.iter(|| {
            black_box(CfgBuilder::extract_from_source(
                black_box(source),
                "python",
                "nested_func",
            ))
        })
    });

    group.finish();
}

fn bench_cfg_exceptions(c: &mut Criterion) {
    let mut group = c.benchmark_group("cfg_exceptions");

    let source = python_exception_handling();
    group.bench_function("python_try_except_finally", |b| {
        b.iter(|| {
            black_box(CfgBuilder::extract_from_source(
                black_box(source),
                "python",
                "exception_func",
            ))
        })
    });

    group.finish();
}

fn bench_cfg_match(c: &mut Criterion) {
    let mut group = c.benchmark_group("cfg_match");

    let source = python_match_statement();
    group.bench_function("python_match_case", |b| {
        b.iter(|| {
            black_box(CfgBuilder::extract_from_source(
                black_box(source),
                "python",
                "match_func",
            ))
        })
    });

    group.finish();
}

fn bench_cfg_complex(c: &mut Criterion) {
    let mut group = c.benchmark_group("cfg_complex");

    let source = python_complex_function();
    group.bench_function("python_all_constructs", |b| {
        b.iter(|| {
            black_box(CfgBuilder::extract_from_source(
                black_box(source),
                "python",
                "complex_func",
            ))
        })
    });

    group.finish();
}

// =============================================================================
// DFG Benchmarks
// =============================================================================

fn bench_dfg_simple_assignments(c: &mut Criterion) {
    let mut group = c.benchmark_group("dfg_simple");

    let source = python_simple_assignments();
    group.bench_function("python_assignments", |b| {
        b.iter(|| {
            black_box(DfgBuilder::extract_from_source(
                black_box(source),
                "python",
                "assign_func",
            ))
        })
    });

    group.finish();
}

fn bench_dfg_many_variables(c: &mut Criterion) {
    let mut group = c.benchmark_group("dfg_many_variables");

    for count in [10, 50, 100] {
        let source = python_many_variables(count);
        group.throughput(Throughput::Elements(count as u64));
        group.bench_with_input(BenchmarkId::new("python", count), &source, |b, source| {
            b.iter(|| {
                black_box(DfgBuilder::extract_from_source(
                    black_box(source),
                    "python",
                    "many_vars_func",
                ))
            })
        });
    }

    group.finish();
}

fn bench_dfg_closures(c: &mut Criterion) {
    let mut group = c.benchmark_group("dfg_closures");

    let source = python_closures();
    group.bench_function("python_lambdas_comprehensions", |b| {
        b.iter(|| {
            black_box(DfgBuilder::extract_from_source(
                black_box(source),
                "python",
                "closure_func",
            ))
        })
    });

    group.finish();
}

fn bench_dfg_pattern_matching(c: &mut Criterion) {
    let mut group = c.benchmark_group("dfg_pattern_matching");

    let source = python_pattern_matching_dfg();
    group.bench_function("python_match_bindings", |b| {
        b.iter(|| {
            black_box(DfgBuilder::extract_from_source(
                black_box(source),
                "python",
                "pattern_func",
            ))
        })
    });

    group.finish();
}

fn bench_dfg_mutations(c: &mut Criterion) {
    let mut group = c.benchmark_group("dfg_mutations");

    let source = python_mutations();
    group.bench_function("python_augmented_assignments", |b| {
        b.iter(|| {
            black_box(DfgBuilder::extract_from_source(
                black_box(source),
                "python",
                "mutation_func",
            ))
        })
    });

    group.finish();
}

// =============================================================================
// Per-Language CFG Benchmarks
// =============================================================================

fn bench_cfg_per_language(c: &mut Criterion) {
    let mut group = c.benchmark_group("cfg_per_language");

    // Python with match/case and comprehensions
    let python_source = python_complex_function();
    group.bench_function("python", |b| {
        b.iter(|| {
            black_box(CfgBuilder::extract_from_source(
                black_box(python_source),
                "python",
                "complex_func",
            ))
        })
    });

    // TypeScript with optional chaining
    let ts_source = typescript_optional_chaining();
    group.bench_function("typescript", |b| {
        b.iter(|| {
            black_box(CfgBuilder::extract_from_source(
                black_box(ts_source),
                "typescript",
                "optionalFunc",
            ))
        })
    });

    // Rust with ? operator and match
    let rust_source = rust_error_handling();
    group.bench_function("rust", |b| {
        b.iter(|| {
            black_box(CfgBuilder::extract_from_source(
                black_box(rust_source),
                "rust",
                "rust_func",
            ))
        })
    });

    // Go with goroutines and defer
    let go_source = go_concurrency();
    group.bench_function("go", |b| {
        b.iter(|| {
            black_box(CfgBuilder::extract_from_source(
                black_box(go_source),
                "go",
                "goFunc",
            ))
        })
    });

    // Java with try-with-resources
    let java_source = java_try_with_resources();
    group.bench_function("java", |b| {
        b.iter(|| {
            black_box(CfgBuilder::extract_from_source(
                black_box(java_source),
                "java",
                "javaFunc",
            ))
        })
    });

    group.finish();
}

// =============================================================================
// Per-Language DFG Benchmarks
// =============================================================================

fn bench_dfg_per_language(c: &mut Criterion) {
    let mut group = c.benchmark_group("dfg_per_language");

    // Python
    let python_source = python_mutations();
    group.bench_function("python", |b| {
        b.iter(|| {
            black_box(DfgBuilder::extract_from_source(
                black_box(python_source),
                "python",
                "mutation_func",
            ))
        })
    });

    // TypeScript
    let ts_source = typescript_optional_chaining();
    group.bench_function("typescript", |b| {
        b.iter(|| {
            black_box(DfgBuilder::extract_from_source(
                black_box(ts_source),
                "typescript",
                "optionalFunc",
            ))
        })
    });

    // Rust
    let rust_source = rust_error_handling();
    group.bench_function("rust", |b| {
        b.iter(|| {
            black_box(DfgBuilder::extract_from_source(
                black_box(rust_source),
                "rust",
                "rust_func",
            ))
        })
    });

    // Go
    let go_source = go_concurrency();
    group.bench_function("go", |b| {
        b.iter(|| {
            black_box(DfgBuilder::extract_from_source(
                black_box(go_source),
                "go",
                "goFunc",
            ))
        })
    });

    // Java
    let java_source = java_try_with_resources();
    group.bench_function("java", |b| {
        b.iter(|| {
            black_box(DfgBuilder::extract_from_source(
                black_box(java_source),
                "java",
                "javaFunc",
            ))
        })
    });

    group.finish();
}

// =============================================================================
// Scaling Benchmarks
// =============================================================================

fn bench_cfg_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("cfg_scaling");
    group.sample_size(50); // Reduce samples for larger functions

    for statements in [10, 100, 500, 1000] {
        let source = python_linear_function(statements);
        group.throughput(Throughput::Elements(statements as u64));
        group.bench_with_input(
            BenchmarkId::new("python_statements", statements),
            &source,
            |b, source| {
                b.iter(|| {
                    black_box(CfgBuilder::extract_from_source(
                        black_box(source),
                        "python",
                        "linear_func",
                    ))
                })
            },
        );
    }

    group.finish();
}

fn bench_dfg_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("dfg_scaling");
    group.sample_size(50); // Reduce samples for larger functions

    for variables in [10, 100, 500, 1000] {
        let source = python_many_variables(variables);
        group.throughput(Throughput::Elements(variables as u64));
        group.bench_with_input(
            BenchmarkId::new("python_variables", variables),
            &source,
            |b, source| {
                b.iter(|| {
                    black_box(DfgBuilder::extract_from_source(
                        black_box(source),
                        "python",
                        "many_vars_func",
                    ))
                })
            },
        );
    }

    group.finish();
}

// =============================================================================
// Program Slicing Benchmarks
// =============================================================================

fn bench_backward_slice(c: &mut Criterion) {
    let mut group = c.benchmark_group("slice_backward");

    // Build DFG once, then benchmark slicing
    let source = python_many_variables(100);
    let dfg = DfgBuilder::extract_from_source(&source, "python", "many_vars_func")
        .expect("Failed to build DFG for slice benchmark");

    // Slice from different positions
    for target_line in [10, 50, 100] {
        group.bench_with_input(
            BenchmarkId::new("line", target_line),
            &target_line,
            |b, &line| b.iter(|| black_box(dfg.backward_slice(black_box(line)))),
        );
    }

    group.finish();
}

fn bench_forward_slice(c: &mut Criterion) {
    let mut group = c.benchmark_group("slice_forward");

    // Build DFG once, then benchmark slicing
    let source = python_many_variables(100);
    let dfg = DfgBuilder::extract_from_source(&source, "python", "many_vars_func")
        .expect("Failed to build DFG for slice benchmark");

    // Slice from different positions
    for source_line in [2, 10, 50] {
        group.bench_with_input(
            BenchmarkId::new("line", source_line),
            &source_line,
            |b, &line| b.iter(|| black_box(dfg.forward_slice(black_box(line)))),
        );
    }

    group.finish();
}

// =============================================================================
// Combined CFG+DFG Benchmarks
// =============================================================================

fn bench_full_flow_analysis(c: &mut Criterion) {
    let mut group = c.benchmark_group("full_flow_analysis");

    let source = python_complex_function();

    group.bench_function("cfg_then_dfg", |b| {
        b.iter(|| {
            let cfg = CfgBuilder::extract_from_source(black_box(source), "python", "complex_func");
            let dfg = DfgBuilder::extract_from_source(black_box(source), "python", "complex_func");
            black_box((cfg, dfg))
        })
    });

    group.finish();
}

// =============================================================================
// Cyclomatic Complexity Benchmarks
// =============================================================================

fn bench_cyclomatic_complexity(c: &mut Criterion) {
    let mut group = c.benchmark_group("cyclomatic_complexity");

    // Build CFGs once
    let simple_source = python_linear_function(10);
    let simple_cfg = CfgBuilder::extract_from_source(&simple_source, "python", "linear_func")
        .expect("Failed to build simple CFG");

    let complex_source = python_complex_function();
    let complex_cfg = CfgBuilder::extract_from_source(complex_source, "python", "complex_func")
        .expect("Failed to build complex CFG");

    group.bench_function("simple_function", |b| {
        b.iter(|| black_box(simple_cfg.cyclomatic_complexity()))
    });

    group.bench_function("complex_function", |b| {
        b.iter(|| black_box(complex_cfg.cyclomatic_complexity()))
    });

    group.finish();
}

// =============================================================================
// CFG/DFG Access Pattern Benchmarks
// =============================================================================

fn bench_cfg_successors_predecessors(c: &mut Criterion) {
    let mut group = c.benchmark_group("cfg_graph_traversal");

    let source = python_complex_function();
    let cfg = CfgBuilder::extract_from_source(source, "python", "complex_func")
        .expect("Failed to build CFG");

    let entry = cfg.entry;

    group.bench_function("successors", |b| {
        b.iter(|| black_box(cfg.successors(black_box(entry))))
    });

    group.bench_function("predecessors", |b| {
        b.iter(|| {
            // Use a non-entry block for predecessors
            let target = cfg.exits.first().copied().unwrap_or(entry);
            black_box(cfg.predecessors(black_box(target)))
        })
    });

    group.finish();
}

fn bench_dfg_variable_lookup(c: &mut Criterion) {
    let mut group = c.benchmark_group("dfg_variable_lookup");

    let source = python_many_variables(100);
    let dfg = DfgBuilder::extract_from_source(&source, "python", "many_vars_func")
        .expect("Failed to build DFG");

    group.bench_function("variables_list", |b| b.iter(|| black_box(dfg.variables())));

    group.bench_function("definitions_lookup", |b| {
        b.iter(|| black_box(dfg.definitions.get("v50")))
    });

    group.bench_function("uses_lookup", |b| b.iter(|| black_box(dfg.uses.get("v50"))));

    group.finish();
}

// =============================================================================
// Criterion Groups and Main
// =============================================================================

criterion_group!(
    cfg_construction_benches,
    bench_cfg_linear,
    bench_cfg_branching,
    bench_cfg_loops,
    bench_cfg_nested,
    bench_cfg_exceptions,
    bench_cfg_match,
    bench_cfg_complex,
);

criterion_group!(
    dfg_construction_benches,
    bench_dfg_simple_assignments,
    bench_dfg_many_variables,
    bench_dfg_closures,
    bench_dfg_pattern_matching,
    bench_dfg_mutations,
);

criterion_group!(
    per_language_benches,
    bench_cfg_per_language,
    bench_dfg_per_language,
);

criterion_group!(scaling_benches, bench_cfg_scaling, bench_dfg_scaling,);

criterion_group!(slicing_benches, bench_backward_slice, bench_forward_slice,);

criterion_group!(
    combined_benches,
    bench_full_flow_analysis,
    bench_cyclomatic_complexity,
    bench_cfg_successors_predecessors,
    bench_dfg_variable_lookup,
);

criterion_main!(
    cfg_construction_benches,
    dfg_construction_benches,
    per_language_benches,
    scaling_benches,
    slicing_benches,
    combined_benches,
);
