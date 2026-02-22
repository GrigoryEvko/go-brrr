use super::*;
use std::io::Write;
use tempfile::NamedTempFile;

use crate::security::common::Severity;

fn scan_cpp(code: &str) -> Vec<CppSafetyFinding> {
    let mut file = NamedTempFile::with_suffix(".cpp").unwrap();
    file.write_all(code.as_bytes()).unwrap();
    file.flush().unwrap();
    let config = CppSafetyConfig::default();
    scan_file_cpp_safety(file.path(), &config).unwrap()
}

fn scan_c(code: &str) -> Vec<CppSafetyFinding> {
    let mut file = NamedTempFile::with_suffix(".c").unwrap();
    file.write_all(code.as_bytes()).unwrap();
    file.flush().unwrap();
    let config = CppSafetyConfig::default();
    scan_file_cpp_safety(file.path(), &config).unwrap()
}

fn findings_with_rule<'a>(findings: &'a [CppSafetyFinding], rule_id: &str) -> Vec<&'a CppSafetyFinding> {
    findings.iter().filter(|f| f.rule_id == rule_id).collect()
}

// ── InitSafe tests ──────────────────────────────────────────────────────

#[test]
fn test_init001_field_without_nsdmi() {
    let findings = scan_cpp(r#"
struct Widget {
    int x;
    float y;
    bool active;
};
"#);
    let init_findings = findings_with_rule(&findings, "INIT-001");
    assert!(!init_findings.is_empty(), "Should flag fields without NSDMI");
}

#[test]
fn test_init001_field_with_nsdmi_clean() {
    let findings = scan_cpp(r#"
struct Widget {
    int x = 0;
    float y = 1.0f;
    bool active = false;
};
"#);
    let init_findings = findings_with_rule(&findings, "INIT-001");
    assert!(init_findings.is_empty(), "Should NOT flag fields with NSDMI");
}

#[test]
fn test_init002_padding_array() {
    let findings = scan_cpp(r#"
struct Packet {
    int type;
    uint8_t padding[3];
};
"#);
    let pad_findings = findings_with_rule(&findings, "INIT-002");
    // padding without {} should be flagged
    assert!(!pad_findings.is_empty(), "Should flag padding array without zero-init");
}

#[test]
fn test_init004_uninit_local() {
    let findings = scan_cpp(r#"
void foo() {
    int result;
    float value;
    result = compute();
}
"#);
    let uninit_findings = findings_with_rule(&findings, "INIT-004");
    assert!(!uninit_findings.is_empty(), "Should flag uninitialized locals");
}

// ── TypeSafe tests ──────────────────────────────────────────────────────

#[test]
fn test_type001_plain_enum() {
    let findings = scan_cpp(r#"
enum Color {
    Red,
    Green,
    Blue
};
"#);
    let type_findings = findings_with_rule(&findings, "TYPE-001");
    assert!(!type_findings.is_empty(), "Should flag plain enum");
}

#[test]
fn test_type001_enum_class_clean() {
    let findings = scan_cpp(r#"
enum class Color {
    Red,
    Green,
    Blue
};
"#);
    let type_findings = findings_with_rule(&findings, "TYPE-001");
    assert!(type_findings.is_empty(), "Should NOT flag enum class");
}

#[test]
fn test_type004_reinterpret_cast() {
    let findings = scan_cpp(r#"
void foo(void* ptr) {
    auto x = reinterpret_cast<int*>(ptr);
}
"#);
    let cast_findings = findings_with_rule(&findings, "TYPE-004");
    assert!(!cast_findings.is_empty(), "Should flag reinterpret_cast");
}

#[test]
fn test_type004_no_reinterpret_cast_clean() {
    let findings = scan_cpp(r#"
void foo(void* ptr) {
    auto x = static_cast<int*>(ptr);
}
"#);
    let cast_findings = findings_with_rule(&findings, "TYPE-004");
    assert!(cast_findings.is_empty(), "Should NOT flag static_cast");
}

// ── NullSafe tests ──────────────────────────────────────────────────────

#[test]
fn test_null002_malloc_no_check() {
    let findings = scan_c(r#"
#include <stdlib.h>
void foo() {
    char *buf = malloc(1024);
    buf[0] = 'a';
}
"#);
    let null_findings = findings_with_rule(&findings, "NULL-002");
    assert!(!null_findings.is_empty(), "Should flag malloc without null check");
}

#[test]
fn test_null002_malloc_with_check_clean() {
    let findings = scan_c(r#"
#include <stdlib.h>
void foo() {
    char *buf = malloc(1024);
    if (buf == NULL) return;
    buf[0] = 'a';
}
"#);
    let null_findings = findings_with_rule(&findings, "NULL-002");
    assert!(null_findings.is_empty(), "Should NOT flag malloc with null check");
}

// ── MemSafe tests ───────────────────────────────────────────────────────

#[test]
fn test_mem001_raw_new() {
    let findings = scan_cpp(r#"
void foo() {
    auto p = new int(42);
}
"#);
    let mem_findings = findings_with_rule(&findings, "MEM-001");
    assert!(!mem_findings.is_empty(), "Should flag raw new");
}

#[test]
fn test_mem001_make_unique_clean() {
    let findings = scan_cpp(r#"
#include <memory>
void foo() {
    auto p = std::make_unique<int>(42);
}
"#);
    let mem_findings = findings_with_rule(&findings, "MEM-001");
    assert!(mem_findings.is_empty(), "Should NOT flag make_unique");
}

#[test]
fn test_mem002_raw_delete() {
    let findings = scan_cpp(r#"
void foo(int* p) {
    delete p;
}
"#);
    let mem_findings = findings_with_rule(&findings, "MEM-002");
    assert!(!mem_findings.is_empty(), "Should flag raw delete");
}

#[test]
fn test_mem003_delete_without_reason() {
    let findings = scan_cpp(r#"
struct NonCopyable {
    NonCopyable(const NonCopyable&) = delete;
    NonCopyable& operator=(const NonCopyable&) = delete;
};
"#);
    let mem_findings = findings_with_rule(&findings, "MEM-003");
    assert!(!mem_findings.is_empty(), "Should flag = delete without reason");
}

#[test]
fn test_mem006_shared_ptr() {
    let findings = scan_cpp(r#"
#include <memory>
void foo() {
    std::shared_ptr<int> p = std::make_shared<int>(42);
}
"#);
    let mem_findings = findings_with_rule(&findings, "MEM-006");
    assert!(!mem_findings.is_empty(), "Should flag std::shared_ptr usage");
}

#[test]
fn test_mem008_alloc_multiply() {
    let findings = scan_c(r#"
#include <stdlib.h>
void foo(size_t count) {
    int *arr = malloc(count * sizeof(int));
}
"#);
    let mem_findings = findings_with_rule(&findings, "MEM-008");
    assert!(!mem_findings.is_empty(), "Should flag unchecked multiplication in malloc");
}

// ── RaceFree tests ──────────────────────────────────────────────────────

#[test]
fn test_race001_mutable_field() {
    let findings = scan_cpp(r#"
class Cache {
    mutable int hits_;
    std::string data_;
};
"#);
    let race_findings = findings_with_rule(&findings, "RACE-001");
    assert!(!race_findings.is_empty(), "Should flag mutable non-sync field");
}

#[test]
fn test_race001_mutable_mutex_clean() {
    let findings = scan_cpp(r#"
class Cache {
    mutable std::mutex mutex_;
    int data_;
};
"#);
    let race_findings = findings_with_rule(&findings, "RACE-001");
    assert!(race_findings.is_empty(), "Should NOT flag mutable mutex");
}

#[test]
fn test_race002_thread_detach() {
    let findings = scan_cpp(r#"
#include <thread>
void foo() {
    std::thread t([]{ /* work */ });
    t.detach();
}
"#);
    let race_findings = findings_with_rule(&findings, "RACE-002");
    assert!(!race_findings.is_empty(), "Should flag thread detach");
}

// ── LeakFree tests ──────────────────────────────────────────────────────

#[test]
fn test_leak001_fopen() {
    let findings = scan_cpp(r#"
#include <cstdio>
void foo() {
    FILE* fp = fopen("data.txt", "r");
    fclose(fp);
}
"#);
    let leak_findings = findings_with_rule(&findings, "LEAK-001");
    assert!(!leak_findings.is_empty(), "Should flag fopen in C++ code");
}

#[test]
fn test_leak002_missing_virtual_dtor() {
    let findings = scan_cpp(r#"
class Base {
public:
    virtual void work() = 0;
    ~Base() {}
};
"#);
    let leak_findings = findings_with_rule(&findings, "LEAK-002");
    assert!(!leak_findings.is_empty(), "Should flag missing virtual destructor");
}

#[test]
fn test_leak002_virtual_dtor_clean() {
    let findings = scan_cpp(r#"
class Base {
public:
    virtual void work() = 0;
    virtual ~Base() = default;
};
"#);
    let leak_findings = findings_with_rule(&findings, "LEAK-002");
    assert!(leak_findings.is_empty(), "Should NOT flag virtual destructor");
}

// ── DetDrop tests ───────────────────────────────────────────────────────

#[test]
fn test_detd001_global_string() {
    let findings = scan_cpp(r#"
static std::string global_name = "hello";
void foo() {}
"#);
    let detd_findings = findings_with_rule(&findings, "DETD-001");
    assert!(!detd_findings.is_empty(), "Should flag static std::string");
}

#[test]
fn test_detd001_constexpr_clean() {
    let findings = scan_cpp(r#"
static constexpr int GLOBAL_CONST = 42;
void foo() {}
"#);
    let detd_findings = findings_with_rule(&findings, "DETD-001");
    assert!(detd_findings.is_empty(), "Should NOT flag constexpr int");
}

// ── Performance tests ───────────────────────────────────────────────────

#[test]
fn test_perf002_atomic_no_alignas() {
    let findings = scan_cpp(r#"
struct Counter {
    std::atomic<int> value;
    int padding;
};
"#);
    let perf_findings = findings_with_rule(&findings, "PERF-002");
    assert!(!perf_findings.is_empty(), "Should flag atomic without alignas");
}

#[test]
fn test_perf002_atomic_with_alignas_clean() {
    let findings = scan_cpp(r#"
struct alignas(64) Counter {
    std::atomic<int> value;
    int padding;
};
"#);
    let perf_findings = findings_with_rule(&findings, "PERF-002");
    assert!(perf_findings.is_empty(), "Should NOT flag atomic with struct alignas");
}

// ── AntiPattern tests ───────────────────────────────────────────────────

#[test]
fn test_anti001_dynamic_cast() {
    let findings = scan_cpp(r#"
class Base { virtual ~Base() = default; };
class Derived : public Base {};
void foo(Base* b) {
    auto d = dynamic_cast<Derived*>(b);
}
"#);
    let anti_findings = findings_with_rule(&findings, "ANTI-001");
    assert!(!anti_findings.is_empty(), "Should flag dynamic_cast");
}

#[test]
fn test_anti003_throw() {
    let findings = scan_cpp(r#"
void foo(int x) {
    if (x < 0) throw std::runtime_error("negative");
}
"#);
    let anti_findings = findings_with_rule(&findings, "ANTI-003");
    assert!(!anti_findings.is_empty(), "Should flag throw statement");
}

// ── Profile/filter tests ────────────────────────────────────────────────

#[test]
fn test_crucible_profile_excludes_perf() {
    let mut file = NamedTempFile::with_suffix(".cpp").unwrap();
    file.write_all(b"
struct Counter {
    std::atomic<int> value;
    int data;
};
void foo() {
    auto p = new int(42);
}
").unwrap();
    file.flush().unwrap();

    let config = CppSafetyConfig {
        profile: CppSafetyProfile::Crucible,
        ..Default::default()
    };
    let findings = scan_file_cpp_safety(file.path(), &config).unwrap();

    // MEM-001 (MemSafe axiom) should be included
    assert!(findings.iter().any(|f| f.rule_id == "MEM-001"));
    // PERF-002 (Performance) should be excluded
    assert!(!findings.iter().any(|f| f.rule_id == "PERF-002"));
}

#[test]
fn test_axiom_filter() {
    let mut file = NamedTempFile::with_suffix(".cpp").unwrap();
    file.write_all(b"
enum Color { Red, Green, Blue };
void foo() {
    auto p = new int(42);
}
").unwrap();
    file.flush().unwrap();

    let config = CppSafetyConfig {
        axiom_filter: Some(SafetyAxiom::TypeSafe),
        ..Default::default()
    };
    let findings = scan_file_cpp_safety(file.path(), &config).unwrap();

    // Only TypeSafe findings should appear
    for f in &findings {
        assert_eq!(f.axiom, SafetyAxiom::TypeSafe, "All findings should be TypeSafe");
    }
}

#[test]
fn test_severity_filter() {
    let mut file = NamedTempFile::with_suffix(".cpp").unwrap();
    file.write_all(b"
void foo() {
    auto p = new int(42);
    auto x = reinterpret_cast<char*>(p);
}
").unwrap();
    file.flush().unwrap();

    let config = CppSafetyConfig {
        min_severity: Severity::High,
        ..Default::default()
    };
    let findings = scan_file_cpp_safety(file.path(), &config).unwrap();

    for f in &findings {
        assert!(f.severity >= Severity::High, "Only High+ findings should appear");
    }
}

#[test]
fn test_c_file_skips_cpp_rules() {
    let findings = scan_c(r#"
enum color { RED, GREEN, BLUE };
void foo() {}
"#);
    // TYPE-001 (plain enum) should NOT fire for C files
    let type_findings = findings_with_rule(&findings, "TYPE-001");
    assert!(type_findings.is_empty(), "Plain enum in C should NOT be flagged");
}

#[test]
fn test_report_axiom_summary() {
    let findings = scan_cpp(r#"
void foo() {
    auto p = new int(42);
    delete p;
}
"#);
    let report = super::build_report(findings, 1);
    assert!(report.axiom_summary.contains_key("MemSafe"));
}

// ── Helper tests ────────────────────────────────────────────────────────

#[test]
fn test_find_pattern_skips_comments() {
    let source = r#"
// reinterpret_cast<int*>(x)
auto y = reinterpret_cast<float*>(z);
"#;
    let matches = super::helpers::find_pattern(source, "reinterpret_cast<");
    assert_eq!(matches.len(), 1, "Should skip commented-out cast");
    assert_eq!(matches[0].line, 3);
}

#[test]
fn test_find_pattern_multiple_matches() {
    let source = "int a; int b; int c;";
    let matches = super::helpers::find_pattern(source, "int ");
    assert_eq!(matches.len(), 3);
}

#[test]
fn test_safety_axiom_display() {
    assert_eq!(SafetyAxiom::MemSafe.to_string(), "MemSafe");
    assert_eq!(SafetyAxiom::RaceFree.to_string(), "RaceFree");
    assert_eq!(SafetyAxiom::DetDrop.to_string(), "DetDrop");
}

#[test]
fn test_safety_axiom_parse() {
    assert_eq!("mem".parse::<SafetyAxiom>().unwrap(), SafetyAxiom::MemSafe);
    assert_eq!("race".parse::<SafetyAxiom>().unwrap(), SafetyAxiom::RaceFree);
    assert_eq!("det".parse::<SafetyAxiom>().unwrap(), SafetyAxiom::DetDrop);
    assert!("invalid".parse::<SafetyAxiom>().is_err());
}

#[test]
fn test_profile_parse() {
    assert_eq!("crucible".parse::<CppSafetyProfile>().unwrap(), CppSafetyProfile::Crucible);
    assert_eq!("standard".parse::<CppSafetyProfile>().unwrap(), CppSafetyProfile::Standard);
}

#[test]
fn test_lookup_rule() {
    let rule = super::rules::lookup_rule("MEM-001").unwrap();
    assert_eq!(rule.axiom, SafetyAxiom::MemSafe);
    assert_eq!(rule.severity, Severity::High);
}

#[test]
fn test_all_rules_have_unique_ids() {
    let mut ids: Vec<&str> = super::rules::RULES.iter().map(|r| r.id).collect();
    let original_len = ids.len();
    ids.sort_unstable();
    ids.dedup();
    assert_eq!(ids.len(), original_len, "Duplicate rule IDs found");
}

// ── Lifetime Safety tests (LIFE-001 to LIFE-004) ─────────────────────

#[test]
fn test_life001_string_view_from_temp_string() {
    let findings = scan_cpp(r#"
void foo() {
    std::string_view sv = std::string("hello");
}
"#);
    let life = findings_with_rule(&findings, "LIFE-001");
    assert!(!life.is_empty(), "Should flag string_view from temporary std::string");
}

#[test]
fn test_life001_string_view_from_substr() {
    let findings = scan_cpp(r#"
void foo(std::string s) {
    std::string_view sv = s.substr(0, 5);
}
"#);
    let life = findings_with_rule(&findings, "LIFE-001");
    assert!(!life.is_empty(), "Should flag string_view from substr (returns temp)");
}

#[test]
fn test_life001_string_view_from_named_ok() {
    let findings = scan_cpp(r#"
void foo() {
    std::string s = "hello";
    std::string_view sv = s;
}
"#);
    let life = findings_with_rule(&findings, "LIFE-001");
    assert!(life.is_empty(), "Should NOT flag string_view from named variable");
}

#[test]
fn test_life002_span_from_temp_vector() {
    let findings = scan_cpp(r#"
void foo() {
    std::span<int> s = std::vector<int>{1, 2, 3};
}
"#);
    let life = findings_with_rule(&findings, "LIFE-002");
    assert!(!life.is_empty(), "Should flag span from temporary vector");
}

#[test]
fn test_life003_view_as_class_member() {
    let findings = scan_cpp(r#"
struct Config {
    std::string_view name;
    int value;
};
"#);
    let life = findings_with_rule(&findings, "LIFE-003");
    assert!(!life.is_empty(), "Should flag string_view as class member");
}

#[test]
fn test_life003_string_member_ok() {
    let findings = scan_cpp(r#"
struct Config {
    std::string name;
    int value;
};
"#);
    let life = findings_with_rule(&findings, "LIFE-003");
    assert!(life.is_empty(), "Should NOT flag std::string as member");
}

#[test]
fn test_life004_return_view_to_local() {
    let findings = scan_cpp(r#"
std::string_view get_name() {
    std::string s = "hello";
    return s;
}
"#);
    let life = findings_with_rule(&findings, "LIFE-004");
    assert!(!life.is_empty(), "Should flag returning string_view to local");
}

#[test]
fn test_life004_return_string_ok() {
    let findings = scan_cpp(r#"
std::string get_name() {
    std::string s = "hello";
    return s;
}
"#);
    let life = findings_with_rule(&findings, "LIFE-004");
    assert!(life.is_empty(), "Should NOT flag returning std::string (owning)");
}

// ── Iterator Invalidation tests (LIFE-005 to LIFE-007) ───────────────

#[test]
fn test_life005_range_for_push_back() {
    let findings = scan_cpp(r#"
void foo(std::vector<int>& vec) {
    for (auto& x : vec) {
        if (x > 0) vec.push_back(x * 2);
    }
}
"#);
    let life = findings_with_rule(&findings, "LIFE-005");
    assert!(!life.is_empty(), "Should flag push_back during range-for");
}

#[test]
fn test_life005_range_for_erase() {
    let findings = scan_cpp(r#"
void foo(std::vector<int>& vec) {
    for (auto& x : vec) {
        vec.erase(vec.begin());
    }
}
"#);
    let life = findings_with_rule(&findings, "LIFE-005");
    assert!(!life.is_empty(), "Should flag erase during range-for");
}

#[test]
fn test_life005_range_for_read_ok() {
    let findings = scan_cpp(r#"
void foo(std::vector<int>& vec) {
    for (auto& x : vec) {
        int y = vec.size();
    }
}
"#);
    let life = findings_with_rule(&findings, "LIFE-005");
    assert!(life.is_empty(), "Should NOT flag read-only access during range-for");
}

#[test]
fn test_life006_iterator_loop_push_back() {
    let findings = scan_cpp(r#"
void foo(std::vector<int>& vec) {
    for (auto it = vec.begin(); it != vec.end(); ++it) {
        vec.push_back(*it);
    }
}
"#);
    let life = findings_with_rule(&findings, "LIFE-006");
    assert!(!life.is_empty(), "Should flag push_back during iterator loop");
}

#[test]
fn test_life006_iterator_loop_no_mutation_ok() {
    let findings = scan_cpp(r#"
void foo(std::vector<int>& vec) {
    for (auto it = vec.begin(); it != vec.end(); ++it) {
        std::cout << *it;
    }
}
"#);
    let life = findings_with_rule(&findings, "LIFE-006");
    assert!(life.is_empty(), "Should NOT flag read-only iterator loop");
}

// ── Initializer List Dangling tests (LIFE-008 to LIFE-010) ───────────

#[test]
fn test_life008_local_initializer_list() {
    let findings = scan_cpp(r#"
void foo() {
    std::initializer_list<int> il = {1, 2, 3};
    use(il);
}
"#);
    let life = findings_with_rule(&findings, "LIFE-008");
    assert!(!life.is_empty(), "Should flag local initializer_list variable");
}

#[test]
fn test_life010_member_initializer_list() {
    let findings = scan_cpp(r#"
struct Widget {
    std::initializer_list<int> values;
    int count;
};
"#);
    let life = findings_with_rule(&findings, "LIFE-010");
    assert!(!life.is_empty(), "Should flag initializer_list as class member");
}

#[test]
fn test_life010_vector_member_ok() {
    let findings = scan_cpp(r#"
struct Widget {
    std::vector<int> values;
    int count;
};
"#);
    let life = findings_with_rule(&findings, "LIFE-010");
    assert!(life.is_empty(), "Should NOT flag std::vector member");
}

// ── Return Ref/Ptr to Local tests (LIFE-011 to LIFE-014) ────────────

#[test]
fn test_life011_return_ref_to_local() {
    let findings = scan_cpp(r#"
const std::string& get_name() {
    std::string name = "hello";
    return name;
}
"#);
    let life = findings_with_rule(&findings, "LIFE-011");
    assert!(!life.is_empty(), "Should flag returning reference to local");
}

#[test]
fn test_life011_return_ptr_to_local() {
    let findings = scan_cpp(r#"
int* get_value() {
    int val = 42;
    return &val;
}
"#);
    let life = findings_with_rule(&findings, "LIFE-011");
    assert!(!life.is_empty(), "Should flag returning pointer to local");
}

#[test]
fn test_life011_return_member_ok() {
    let findings = scan_cpp(r#"
class Foo {
    std::string name_;
    const std::string& get_name() {
        return name_;
    }
};
"#);
    let life = findings_with_rule(&findings, "LIFE-011");
    assert!(life.is_empty(), "Should NOT flag returning reference to member");
}

#[test]
fn test_life013_lambda_ref_escape() {
    let findings = scan_cpp(r#"
std::function<void()> make_func() {
    int x = 42;
    return std::function<void()>([&] { use(x); });
}
"#);
    let life = findings_with_rule(&findings, "LIFE-013");
    assert!(!life.is_empty(), "Should flag lambda [&] escaping via std::function return");
}

#[test]
fn test_life013_lambda_value_capture_ok() {
    let findings = scan_cpp(r#"
std::function<void()> make_func() {
    int x = 42;
    return std::function<void()>([=] { use(x); });
}
"#);
    let life = findings_with_rule(&findings, "LIFE-013");
    assert!(life.is_empty(), "Should NOT flag lambda [=] (value capture)");
}

// ── Unsafe Context tests (UCTX-001 to UCTX-006) ────────────────────────

#[test]
fn test_uctx001_pointer_arithmetic() {
    let findings = scan_cpp(r#"
void process(int* data, int n) {
    int val = *(data + 3);
    int val2 = *(data - 1);
}
"#);
    let uctx = findings_with_rule(&findings, "UCTX-001");
    assert!(uctx.len() >= 2, "Should flag *(ptr + n) and *(ptr - n)");
}

#[test]
fn test_uctx001_no_false_positive_on_normal_math() {
    let findings = scan_cpp(r#"
int compute(int a, int b) {
    return a + b;
}
"#);
    let uctx = findings_with_rule(&findings, "UCTX-001");
    assert!(uctx.is_empty(), "Should NOT flag regular integer arithmetic");
}

#[test]
fn test_uctx004_union_definition() {
    let findings = scan_cpp(r#"
union Value {
    int i;
    float f;
    char* s;
};
"#);
    let uctx = findings_with_rule(&findings, "UCTX-004");
    assert!(!uctx.is_empty(), "Should flag union definition");
}

#[test]
fn test_uctx005_mutable_static() {
    let findings = scan_cpp(r#"
static int counter = 0;
static const int MAX = 100;
static constexpr int SIZE = 64;
"#);
    let uctx = findings_with_rule(&findings, "UCTX-005");
    assert_eq!(uctx.len(), 1, "Should flag only the mutable static, not const/constexpr");
}

#[test]
fn test_uctx006_inline_assembly() {
    let findings = scan_cpp(r#"
void barrier() {
    asm volatile("mfence" ::: "memory");
}
void other() {
    __asm__("nop");
}
"#);
    let uctx = findings_with_rule(&findings, "UCTX-006");
    assert!(uctx.len() >= 2, "Should flag both asm volatile and __asm__");
}

#[test]
fn test_uctx006_no_false_positive() {
    let findings = scan_cpp(r#"
// This is an asm comment
void assemble_data() {
    int x = 42;
}
"#);
    let uctx = findings_with_rule(&findings, "UCTX-006");
    assert!(uctx.is_empty(), "Should NOT flag function with 'asm' in name or comment");
}

// ── TSAF: Type Safety Extension tests ─────────────────────────────────

#[test]
fn test_tsaf001_optional_unchecked_value() {
    let findings = scan_cpp(r#"
#include <optional>
std::optional<int> get_value();
void use_it() {
    auto opt = get_value();
    int x = opt.value();
}
"#);
    let tsaf = findings_with_rule(&findings, "TSAF-001");
    assert!(!tsaf.is_empty(), "Should flag .value() on optional without has_value() check");
}

#[test]
fn test_tsaf001_optional_guarded_clean() {
    let findings = scan_cpp(r#"
#include <optional>
void safe_use(std::optional<int> opt) {
    if (opt.has_value()) {
        int x = opt.value();
    }
}
"#);
    let tsaf = findings_with_rule(&findings, "TSAF-001");
    assert!(tsaf.is_empty(), "Should NOT flag .value() guarded by has_value()");
}

#[test]
fn test_tsaf001_optional_boolean_guard_clean() {
    let findings = scan_cpp(r#"
#include <optional>
void safe_use(std::optional<int> opt) {
    if (opt) {
        int x = opt.value();
    }
}
"#);
    let tsaf = findings_with_rule(&findings, "TSAF-001");
    assert!(tsaf.is_empty(), "Should NOT flag .value() guarded by if(opt)");
}

#[test]
fn test_tsaf001_value_or_clean() {
    let findings = scan_cpp(r#"
#include <optional>
void safe_use(std::optional<int> opt) {
    int x = opt.value_or(42);
}
"#);
    let tsaf = findings_with_rule(&findings, "TSAF-001");
    assert!(tsaf.is_empty(), "Should NOT flag .value_or()");
}

#[test]
fn test_tsaf003_variant_get_unchecked() {
    let findings = scan_cpp(r#"
#include <variant>
void use_variant(std::variant<int, std::string> v) {
    int x = std::get<int>(v);
}
"#);
    let tsaf = findings_with_rule(&findings, "TSAF-003");
    assert!(!tsaf.is_empty(), "Should flag std::get without holds_alternative check");
}

#[test]
fn test_tsaf003_variant_get_guarded_clean() {
    let findings = scan_cpp(r#"
#include <variant>
void safe_use(std::variant<int, std::string> v) {
    if (std::holds_alternative<int>(v)) {
        int x = std::get<int>(v);
    }
}
"#);
    let tsaf = findings_with_rule(&findings, "TSAF-003");
    assert!(tsaf.is_empty(), "Should NOT flag std::get guarded by holds_alternative");
}

#[test]
fn test_tsaf003_variant_visit_clean() {
    let findings = scan_cpp(r#"
#include <variant>
void safe_use(std::variant<int, std::string> v) {
    std::visit([](auto& val) { /* handle */ }, v);
}
"#);
    let tsaf = findings_with_rule(&findings, "TSAF-003");
    assert!(tsaf.is_empty(), "Should NOT flag std::visit usage");
}

#[test]
fn test_tsaf004_smart_ptr_unchecked() {
    let findings = scan_cpp(r#"
#include <memory>
void use_ptr() {
    std::unique_ptr<int> ptr = make_unique<int>(42);
    ptr->do_something();
    int x = *ptr;
}
"#);
    let tsaf = findings_with_rule(&findings, "TSAF-004");
    assert!(!tsaf.is_empty(), "Should flag smart pointer deref without null check");
}

#[test]
fn test_tsaf004_smart_ptr_guarded_clean() {
    let findings = scan_cpp(r#"
#include <memory>
void safe_use(std::unique_ptr<int> ptr) {
    if (ptr != nullptr) {
        int x = *ptr;
    }
}
"#);
    let tsaf = findings_with_rule(&findings, "TSAF-004");
    assert!(tsaf.is_empty(), "Should NOT flag smart pointer deref guarded by null check");
}

#[test]
fn test_tsaf005_any_cast_unchecked() {
    let findings = scan_cpp(r#"
#include <any>
void use_any(std::any a) {
    int x = std::any_cast<int>(a);
}
"#);
    let tsaf = findings_with_rule(&findings, "TSAF-005");
    assert!(!tsaf.is_empty(), "Should flag any_cast without type check");
}

#[test]
fn test_tsaf005_any_cast_pointer_form_clean() {
    let findings = scan_cpp(r#"
#include <any>
void safe_use(std::any a) {
    auto* p = std::any_cast<int>(&a);
    if (p) { /* safe */ }
}
"#);
    let tsaf = findings_with_rule(&findings, "TSAF-005");
    assert!(tsaf.is_empty(), "Should NOT flag any_cast with pointer form (address-of argument)");
}

// ── TSAF: Pattern Matching tests ──────────────────────────────────────

#[test]
fn test_tsaf007_switch_implicit_fallthrough() {
    let findings = scan_cpp(r#"
void process(int x) {
    switch (x) {
        case 1:
            do_something();
        case 2:
            do_other();
            break;
    }
}
"#);
    let tsaf = findings_with_rule(&findings, "TSAF-007");
    assert!(!tsaf.is_empty(), "Should flag case 1 without break (implicit fallthrough)");
}

#[test]
fn test_tsaf007_switch_with_break_clean() {
    let findings = scan_cpp(r#"
void process(int x) {
    switch (x) {
        case 1:
            do_something();
            break;
        case 2:
            do_other();
            break;
    }
}
"#);
    let tsaf = findings_with_rule(&findings, "TSAF-007");
    assert!(tsaf.is_empty(), "Should NOT flag cases with break");
}

#[test]
fn test_tsaf007_switch_with_return_clean() {
    let findings = scan_cpp(r#"
int process(int x) {
    switch (x) {
        case 1:
            return 10;
        case 2:
            return 20;
    }
    return 0;
}
"#);
    let tsaf = findings_with_rule(&findings, "TSAF-007");
    assert!(tsaf.is_empty(), "Should NOT flag cases with return");
}

#[test]
fn test_tsaf007_switch_fallthrough_attribute_clean() {
    let findings = scan_cpp(r#"
void process(int x) {
    switch (x) {
        case 1:
            do_something();
            [[fallthrough]];
        case 2:
            do_other();
            break;
    }
}
"#);
    let tsaf = findings_with_rule(&findings, "TSAF-007");
    assert!(tsaf.is_empty(), "Should NOT flag [[fallthrough]] attributed cases");
}

#[test]
fn test_tsaf007_empty_case_grouping_clean() {
    let findings = scan_cpp(r#"
void process(int x) {
    switch (x) {
        case 1:
        case 2:
        case 3:
            do_something();
            break;
    }
}
"#);
    let tsaf = findings_with_rule(&findings, "TSAF-007");
    assert!(tsaf.is_empty(), "Should NOT flag empty case labels (intentional grouping)");
}

#[test]
fn test_tsaf008_switch_on_bool() {
    let findings = scan_cpp(r#"
void process(bool b) {
    switch (b) {
        case true:
            yes();
            break;
        case false:
            no();
            break;
    }
}
"#);
    let tsaf = findings_with_rule(&findings, "TSAF-008");
    assert!(!tsaf.is_empty(), "Should flag switch on bool");
}

#[test]
fn test_tsaf009_switch_no_default() {
    let findings = scan_cpp(r#"
void process(int x) {
    switch (x) {
        case 1:
            a();
            break;
        case 2:
            b();
            break;
    }
}
"#);
    let tsaf = findings_with_rule(&findings, "TSAF-009");
    assert!(!tsaf.is_empty(), "Should flag switch without default case");
}

#[test]
fn test_tsaf009_switch_with_default_clean() {
    let findings = scan_cpp(r#"
void process(int x) {
    switch (x) {
        case 1:
            a();
            break;
        default:
            fallback();
            break;
    }
}
"#);
    let tsaf = findings_with_rule(&findings, "TSAF-009");
    assert!(tsaf.is_empty(), "Should NOT flag switch with default case");
    let tsaf6 = findings_with_rule(&findings, "TSAF-006");
    assert!(tsaf6.is_empty(), "Should NOT flag TSAF-006 either when default is present");
}

#[test]
fn test_tsaf006_enum_switch_no_default() {
    let findings = scan_cpp(r#"
enum class Color { Red, Green, Blue };
void paint(Color c) {
    switch (c) {
        case Color::Red:
            red();
            break;
        case Color::Green:
            green();
            break;
    }
}
"#);
    let tsaf = findings_with_rule(&findings, "TSAF-006");
    assert!(!tsaf.is_empty(), "Should flag enum switch without default (missing Blue case)");
}
