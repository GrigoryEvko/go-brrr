//! Rust-specific taint sink definitions.
//!
//! This module contains comprehensive sink definitions for Rust security analysis,
//! covering standard library and popular frameworks:
//!
//! - **SQL**: sqlx, diesel, sea-orm, rusqlite
//! - **Web**: Actix-web, Axum, Rocket, Warp
//! - **Command**: std::process::Command
//! - **File**: std::fs, tokio::fs
//! - **Network**: reqwest, hyper
//! - **Template**: tera, askama, handlebars
//!
//! Note: Rust's type system and borrow checker prevent many vulnerabilities
//! at compile time. However, `unsafe` blocks and certain runtime operations
//! can still introduce security issues.

use super::{Sink, SinkCategory, SinkRegistry};

/// Build the complete Rust sink registry.
pub fn get_rust_sinks() -> SinkRegistry {
    let mut registry = SinkRegistry::new();

    // Add all sink categories
    add_sql_sinks(&mut registry);
    add_command_sinks(&mut registry);
    add_path_sinks(&mut registry);
    add_ssrf_sinks(&mut registry);
    add_deserialization_sinks(&mut registry);
    add_template_sinks(&mut registry);
    add_unsafe_sinks(&mut registry);
    add_web_sinks(&mut registry);

    registry
}

// =============================================================================
// SQL Injection Sinks
// =============================================================================

fn add_sql_sinks(registry: &mut SinkRegistry) {
    // sqlx - the most popular async SQL crate
    registry.add(Sink::sql("sqlx::query(", "sqlx query() with string").with_severity(9));
    registry
        .add(Sink::sql("sqlx::query_as(", "sqlx query_as() with string").with_severity(9));
    registry.add(
        Sink::sql("sqlx::query_scalar(", "sqlx query_scalar() with string").with_severity(9),
    );
    registry.add(Sink::sql(".execute(", "sqlx execute()"));
    registry.add(Sink::sql(".fetch_one(", "sqlx fetch_one()"));
    registry.add(Sink::sql(".fetch_all(", "sqlx fetch_all()"));
    registry.add(Sink::sql(".fetch_optional(", "sqlx fetch_optional()"));
    registry.add(Sink::sql(".fetch(", "sqlx fetch()"));
    // Note: sqlx::query!() and sqlx::query_as!() are compile-time checked and safe

    // diesel
    registry.add(
        Sink::sql("diesel::sql_query(", "diesel sql_query() raw SQL").with_severity(9),
    );
    registry.add(Sink::sql("diesel::dsl::sql(", "diesel dsl::sql()").with_severity(8));
    registry.add(Sink::sql(".execute(", "diesel execute()"));
    registry.add(Sink::sql(".load::<", "diesel load()"));
    registry.add(Sink::sql(".get_result(", "diesel get_result()"));

    // sea-orm
    registry.add(
        Sink::sql("Statement::from_string(", "sea-orm raw SQL statement").with_severity(9),
    );
    registry.add(
        Sink::sql("Statement::from_sql_and_values(", "sea-orm raw SQL").with_severity(9),
    );
    registry.add(
        Sink::sql("db.execute(Statement::from_string", "sea-orm execute raw").with_severity(9),
    );

    // rusqlite
    registry.add(Sink::sql("conn.execute(", "rusqlite execute()"));
    registry.add(Sink::sql("conn.query_row(", "rusqlite query_row()"));
    registry.add(Sink::sql("conn.prepare(", "rusqlite prepare()"));
    registry.add(Sink::sql("stmt.execute(", "rusqlite stmt.execute()"));
    registry.add(Sink::sql("stmt.query(", "rusqlite stmt.query()"));

    // tokio-postgres
    registry.add(Sink::sql("client.query(", "tokio-postgres query()"));
    registry.add(Sink::sql("client.query_one(", "tokio-postgres query_one()"));
    registry.add(Sink::sql("client.execute(", "tokio-postgres execute()"));
    registry.add(Sink::sql("client.simple_query(", "tokio-postgres simple_query()"));

    // mysql_async
    registry.add(Sink::sql("conn.query(", "mysql_async query()"));
    registry.add(Sink::sql("conn.exec(", "mysql_async exec()"));
    registry.add(Sink::sql("conn.query_iter(", "mysql_async query_iter()"));
}

// =============================================================================
// Command Injection Sinks
// =============================================================================

fn add_command_sinks(registry: &mut SinkRegistry) {
    // std::process::Command
    registry.add(Sink::command("Command::new(", "std::process::Command::new()"));
    registry.add(Sink::command("std::process::Command::new(", "std::process::Command::new()"));
    registry.add(Sink::command(".arg(", "Command.arg()").with_severity(7));
    registry.add(Sink::command(".args(", "Command.args()").with_severity(7));
    registry.add(Sink::command(".env(", "Command.env()").with_severity(5));
    registry.add(Sink::command(".current_dir(", "Command.current_dir()").with_severity(5));

    // tokio::process::Command (async version)
    registry.add(Sink::command(
        "tokio::process::Command::new(",
        "tokio::process::Command::new()",
    ));

    // duct (shell command library)
    registry.add(Sink::command("duct::cmd(", "duct::cmd()"));
    registry.add(Sink::command("cmd!(", "duct cmd!() macro").with_severity(10));

    // shell-words/shlex for parsing
    registry.add(Sink::command("shell_words::join(", "shell_words join()").with_severity(6));
}

// =============================================================================
// Path Traversal Sinks
// =============================================================================

fn add_path_sinks(registry: &mut SinkRegistry) {
    // std::fs operations
    registry.add(Sink::path("std::fs::read(", "std::fs::read()"));
    registry.add(Sink::path("std::fs::read_to_string(", "std::fs::read_to_string()"));
    registry.add(Sink::path("std::fs::write(", "std::fs::write()"));
    registry.add(Sink::path("std::fs::remove_file(", "std::fs::remove_file()"));
    registry.add(Sink::path("std::fs::remove_dir(", "std::fs::remove_dir()"));
    registry.add(
        Sink::path("std::fs::remove_dir_all(", "std::fs::remove_dir_all()").with_severity(9),
    );
    registry.add(Sink::path("std::fs::create_dir(", "std::fs::create_dir()"));
    registry
        .add(Sink::path("std::fs::create_dir_all(", "std::fs::create_dir_all()"));
    registry.add(Sink::path("std::fs::rename(", "std::fs::rename()"));
    registry.add(Sink::path("std::fs::copy(", "std::fs::copy()"));
    registry.add(Sink::path("std::fs::hard_link(", "std::fs::hard_link()"));
    registry.add(Sink::path("std::fs::read_link(", "std::fs::read_link()"));
    registry.add(Sink::path("std::fs::metadata(", "std::fs::metadata()"));
    registry.add(Sink::path("std::fs::symlink_metadata(", "std::fs::symlink_metadata()"));
    registry.add(Sink::path("std::fs::read_dir(", "std::fs::read_dir()"));
    registry.add(Sink::path("std::fs::canonicalize(", "std::fs::canonicalize()"));

    // Short forms (after use std::fs::*;)
    registry.add(Sink::path("fs::read(", "fs::read()"));
    registry.add(Sink::path("fs::read_to_string(", "fs::read_to_string()"));
    registry.add(Sink::path("fs::write(", "fs::write()"));
    registry.add(Sink::path("fs::remove_file(", "fs::remove_file()"));
    registry.add(Sink::path("fs::remove_dir_all(", "fs::remove_dir_all()").with_severity(9));

    // File operations
    registry.add(Sink::path("File::open(", "std::fs::File::open()"));
    registry.add(Sink::path("File::create(", "std::fs::File::create()"));
    registry.add(Sink::path("OpenOptions::new(", "std::fs::OpenOptions"));

    // tokio::fs (async versions)
    registry.add(Sink::path("tokio::fs::read(", "tokio::fs::read()"));
    registry.add(Sink::path("tokio::fs::read_to_string(", "tokio::fs::read_to_string()"));
    registry.add(Sink::path("tokio::fs::write(", "tokio::fs::write()"));
    registry.add(Sink::path("tokio::fs::remove_file(", "tokio::fs::remove_file()"));
    registry.add(
        Sink::path("tokio::fs::remove_dir_all(", "tokio::fs::remove_dir_all()").with_severity(9),
    );
    registry.add(Sink::path("tokio::fs::File::open(", "tokio::fs::File::open()"));
    registry.add(Sink::path("tokio::fs::File::create(", "tokio::fs::File::create()"));

    // Path construction (lower severity)
    registry.add(Sink::path("Path::new(", "std::path::Path::new()").with_severity(4));
    registry.add(Sink::path("PathBuf::from(", "std::path::PathBuf::from()").with_severity(4));
    registry.add(Sink::path(".join(", "Path::join()").with_severity(5));
    registry.add(Sink::path(".push(", "PathBuf::push()").with_severity(5));

    // Archive extraction
    registry.add(Sink::path("ZipArchive::new(", "zip ZipArchive").with_severity(7));
    registry.add(Sink::path("Archive::new(", "tar Archive").with_severity(7));
    registry.add(Sink::path(".unpack(", "tar unpack()").with_severity(9));
    registry.add(Sink::path(".extract(", "zip extract()").with_severity(9));

    // tempfile
    registry.add(Sink::path("tempfile::Builder::new(", "tempfile Builder").with_severity(4));

    // include_* macros (compile-time, but path is hardcoded)
    registry.add(Sink::path("include_str!(", "include_str!()").with_severity(3));
    registry.add(Sink::path("include_bytes!(", "include_bytes!()").with_severity(3));
}

// =============================================================================
// SSRF Sinks
// =============================================================================

fn add_ssrf_sinks(registry: &mut SinkRegistry) {
    // reqwest (most popular HTTP client)
    registry.add(Sink::ssrf("reqwest::get(", "reqwest::get()"));
    registry.add(Sink::ssrf("reqwest::Client::new(", "reqwest Client"));
    registry.add(Sink::ssrf("client.get(", "reqwest client.get()"));
    registry.add(Sink::ssrf("client.post(", "reqwest client.post()"));
    registry.add(Sink::ssrf("client.put(", "reqwest client.put()"));
    registry.add(Sink::ssrf("client.delete(", "reqwest client.delete()"));
    registry.add(Sink::ssrf("client.request(", "reqwest client.request()"));
    registry.add(Sink::ssrf("RequestBuilder::send(", "reqwest send()"));
    registry.add(Sink::ssrf(".send().await", "reqwest send().await"));

    // hyper
    registry.add(Sink::ssrf("hyper::Client::new(", "hyper Client"));
    registry.add(Sink::ssrf("hyper::Request::builder(", "hyper Request builder"));
    registry.add(Sink::ssrf("client.request(", "hyper client.request()"));

    // ureq (blocking HTTP client)
    registry.add(Sink::ssrf("ureq::get(", "ureq::get()"));
    registry.add(Sink::ssrf("ureq::post(", "ureq::post()"));
    registry.add(Sink::ssrf("ureq::agent(", "ureq agent"));

    // surf
    registry.add(Sink::ssrf("surf::get(", "surf::get()"));
    registry.add(Sink::ssrf("surf::post(", "surf::post()"));

    // awc (actix-web client)
    registry.add(Sink::ssrf("awc::Client::new(", "awc Client"));
    registry.add(Sink::ssrf("client.get(", "awc client.get()"));
    registry.add(Sink::ssrf("client.post(", "awc client.post()"));

    // std::net
    registry.add(Sink::ssrf("TcpStream::connect(", "TcpStream::connect()"));
    registry.add(Sink::ssrf("UdpSocket::connect(", "UdpSocket::connect()"));
    registry.add(Sink::ssrf("UnixStream::connect(", "UnixStream::connect()"));

    // tokio::net
    registry.add(Sink::ssrf("tokio::net::TcpStream::connect(", "tokio TcpStream::connect()"));
}

// =============================================================================
// Deserialization Sinks
// =============================================================================

fn add_deserialization_sinks(registry: &mut SinkRegistry) {
    // serde_json (generally safe, but included for completeness)
    registry.add(
        Sink::new("serde_json::from_str(", SinkCategory::Deserialization).with_severity(4),
    );
    registry.add(
        Sink::new("serde_json::from_slice(", SinkCategory::Deserialization).with_severity(4),
    );
    registry.add(
        Sink::new("serde_json::from_reader(", SinkCategory::Deserialization).with_severity(4),
    );

    // serde_yaml
    registry.add(
        Sink::new("serde_yaml::from_str(", SinkCategory::Deserialization).with_severity(5),
    );
    registry.add(
        Sink::new("serde_yaml::from_slice(", SinkCategory::Deserialization).with_severity(5),
    );
    registry.add(
        Sink::new("serde_yaml::from_reader(", SinkCategory::Deserialization).with_severity(5),
    );

    // toml
    registry.add(
        Sink::new("toml::from_str(", SinkCategory::Deserialization).with_severity(4),
    );

    // bincode (binary format)
    registry.add(
        Sink::new("bincode::deserialize(", SinkCategory::Deserialization).with_severity(6),
    );
    registry.add(
        Sink::new("bincode::deserialize_from(", SinkCategory::Deserialization).with_severity(6),
    );

    // postcard (embedded binary format)
    registry.add(
        Sink::new("postcard::from_bytes(", SinkCategory::Deserialization).with_severity(5),
    );

    // rmp-serde (MessagePack)
    registry.add(
        Sink::new("rmp_serde::from_slice(", SinkCategory::Deserialization).with_severity(5),
    );
    registry.add(
        Sink::new("rmp_serde::decode::from_read(", SinkCategory::Deserialization)
            .with_severity(5),
    );

    // ciborium (CBOR)
    registry.add(
        Sink::new("ciborium::de::from_reader(", SinkCategory::Deserialization).with_severity(5),
    );

    // quick-xml
    registry.add(
        Sink::new("quick_xml::de::from_str(", SinkCategory::Deserialization).with_severity(6),
    );
    registry.add(
        Sink::new("quick_xml::de::from_reader(", SinkCategory::Deserialization).with_severity(6),
    );
}

// =============================================================================
// Template Injection Sinks
// =============================================================================

fn add_template_sinks(registry: &mut SinkRegistry) {
    // tera
    registry.add(
        Sink::new("Tera::new(", SinkCategory::TemplateInjection).with_severity(6),
    );
    registry.add(
        Sink::new("tera.render(", SinkCategory::TemplateInjection).with_severity(5),
    );
    registry.add(
        Sink::new("tera.render_str(", SinkCategory::TemplateInjection).with_severity(8),
    );
    registry.add(
        Sink::new("Tera::one_off(", SinkCategory::TemplateInjection).with_severity(8),
    );

    // handlebars
    registry.add(
        Sink::new("handlebars.render_template(", SinkCategory::TemplateInjection)
            .with_severity(8),
    );
    registry.add(
        Sink::new("handlebars.render(", SinkCategory::TemplateInjection).with_severity(5),
    );
    registry.add(
        Sink::new("Handlebars::new(", SinkCategory::TemplateInjection).with_severity(5),
    );

    // askama (compile-time templates - generally safe)
    // Not included as it's compile-time checked

    // minijinja
    registry.add(
        Sink::new("Environment::new(", SinkCategory::TemplateInjection).with_severity(5),
    );
    registry.add(
        Sink::new("env.render_str(", SinkCategory::TemplateInjection).with_severity(8),
    );

    // liquid
    registry.add(
        Sink::new("liquid::ParserBuilder::new(", SinkCategory::TemplateInjection)
            .with_severity(5),
    );
    registry.add(
        Sink::new("template.render(", SinkCategory::TemplateInjection).with_severity(5),
    );
}

// =============================================================================
// Unsafe/Memory Sinks
// =============================================================================

fn add_unsafe_sinks(registry: &mut SinkRegistry) {
    // std::ptr operations
    registry.add(
        Sink::new("std::ptr::read(", SinkCategory::MemoryCorruption).with_severity(9),
    );
    registry.add(
        Sink::new("std::ptr::read_unaligned(", SinkCategory::MemoryCorruption).with_severity(9),
    );
    registry.add(
        Sink::new("std::ptr::read_volatile(", SinkCategory::MemoryCorruption).with_severity(9),
    );
    registry.add(
        Sink::new("std::ptr::write(", SinkCategory::MemoryCorruption).with_severity(9),
    );
    registry.add(
        Sink::new("std::ptr::write_unaligned(", SinkCategory::MemoryCorruption)
            .with_severity(9),
    );
    registry.add(
        Sink::new("std::ptr::write_volatile(", SinkCategory::MemoryCorruption).with_severity(9),
    );
    registry.add(
        Sink::new("std::ptr::copy(", SinkCategory::MemoryCorruption).with_severity(9),
    );
    registry.add(
        Sink::new("std::ptr::copy_nonoverlapping(", SinkCategory::MemoryCorruption)
            .with_severity(9),
    );
    registry.add(
        Sink::new("std::ptr::swap(", SinkCategory::MemoryCorruption).with_severity(8),
    );
    registry.add(
        Sink::new("std::ptr::replace(", SinkCategory::MemoryCorruption).with_severity(8),
    );

    // Short forms
    registry.add(
        Sink::new("ptr::read(", SinkCategory::MemoryCorruption).with_severity(9),
    );
    registry.add(
        Sink::new("ptr::write(", SinkCategory::MemoryCorruption).with_severity(9),
    );

    // std::mem operations
    registry.add(
        Sink::new("std::mem::transmute(", SinkCategory::MemoryCorruption).with_severity(10),
    );
    registry.add(
        Sink::new("std::mem::transmute_copy(", SinkCategory::MemoryCorruption).with_severity(10),
    );
    registry.add(
        Sink::new("std::mem::zeroed(", SinkCategory::MemoryCorruption).with_severity(8),
    );
    registry.add(
        Sink::new("std::mem::uninitialized(", SinkCategory::MemoryCorruption).with_severity(10),
    );
    registry.add(
        Sink::new("std::mem::forget(", SinkCategory::MemoryCorruption).with_severity(7),
    );

    // Short forms
    registry.add(
        Sink::new("mem::transmute(", SinkCategory::MemoryCorruption).with_severity(10),
    );
    registry.add(
        Sink::new("mem::zeroed(", SinkCategory::MemoryCorruption).with_severity(8),
    );

    // Raw pointer operations
    registry.add(
        Sink::new(".as_ptr()", SinkCategory::MemoryCorruption)
            .with_severity(5)
            .with_tag("raw-pointer"),
    );
    registry.add(
        Sink::new(".as_mut_ptr()", SinkCategory::MemoryCorruption)
            .with_severity(6)
            .with_tag("raw-pointer"),
    );
    registry.add(
        Sink::new("as *const", SinkCategory::MemoryCorruption)
            .with_severity(6)
            .with_tag("raw-pointer"),
    );
    registry.add(
        Sink::new("as *mut", SinkCategory::MemoryCorruption)
            .with_severity(7)
            .with_tag("raw-pointer"),
    );

    // Box/Vec from raw
    registry.add(
        Sink::new("Box::from_raw(", SinkCategory::MemoryCorruption).with_severity(9),
    );
    registry.add(
        Sink::new("Vec::from_raw_parts(", SinkCategory::MemoryCorruption).with_severity(9),
    );
    registry.add(
        Sink::new("String::from_raw_parts(", SinkCategory::MemoryCorruption).with_severity(9),
    );

    // slice::from_raw_parts
    registry.add(
        Sink::new("slice::from_raw_parts(", SinkCategory::MemoryCorruption).with_severity(9),
    );
    registry.add(
        Sink::new("slice::from_raw_parts_mut(", SinkCategory::MemoryCorruption)
            .with_severity(9),
    );
}

// =============================================================================
// Web Framework Sinks
// =============================================================================

fn add_web_sinks(registry: &mut SinkRegistry) {
    // Actix-web XSS (HTML responses)
    registry.add(
        Sink::new("HttpResponse::Ok().body(", SinkCategory::XSS)
            .with_severity(5),
    );
    registry.add(
        Sink::new("HttpResponse::build(", SinkCategory::XSS)
            .with_severity(5),
    );
    registry.add(
        Sink::new("web::Html(", SinkCategory::XSS)
            .with_severity(6),
    );

    // Axum
    registry.add(
        Sink::new("axum::response::Html(", SinkCategory::XSS)
            .with_severity(6),
    );
    registry.add(
        Sink::new("Response::builder(", SinkCategory::XSS)
            .with_severity(5),
    );

    // Rocket
    registry.add(
        Sink::new("rocket::response::content::RawHtml(", SinkCategory::XSS)
            .with_severity(7),
    );

    // Warp
    registry.add(
        Sink::new("warp::reply::html(", SinkCategory::XSS)
            .with_severity(6),
    );
    registry.add(
        Sink::new("warp::reply::with_header(", SinkCategory::HeaderInjection)
            .with_severity(5),
    );

    // Redirect sinks
    registry.add(
        Sink::new("Redirect::to(", SinkCategory::OpenRedirect)
            .with_dangerous_params(vec![0]),
    );
    registry.add(
        Sink::new("Redirect::permanent(", SinkCategory::OpenRedirect)
            .with_dangerous_params(vec![0]),
    );
    registry.add(
        Sink::new("Redirect::temporary(", SinkCategory::OpenRedirect)
            .with_dangerous_params(vec![0]),
    );

    // Header sinks
    registry.add(
        Sink::new(".insert_header(", SinkCategory::HeaderInjection)
            .with_severity(5),
    );
    registry.add(
        Sink::new(".append_header(", SinkCategory::HeaderInjection)
            .with_severity(5),
    );
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rust_sql_sinks() {
        let registry = get_rust_sinks();

        let matches = registry.find_matches("sqlx::query(");
        assert!(!matches.is_empty());
        assert!(matches
            .iter()
            .any(|s| s.category == SinkCategory::SqlInjection));
    }

    #[test]
    fn test_rust_command_sinks() {
        let registry = get_rust_sinks();

        let matches = registry.find_matches("Command::new(");
        assert!(!matches.is_empty());
        assert!(matches
            .iter()
            .any(|s| s.category == SinkCategory::CommandInjection));
    }

    #[test]
    fn test_rust_path_sinks() {
        let registry = get_rust_sinks();

        let matches = registry.find_matches("std::fs::read(");
        assert!(!matches.is_empty());
        assert!(matches
            .iter()
            .any(|s| s.category == SinkCategory::PathTraversal));
    }

    #[test]
    fn test_rust_ssrf_sinks() {
        let registry = get_rust_sinks();

        let matches = registry.find_matches("reqwest::get(");
        assert!(!matches.is_empty());
        assert!(matches.iter().any(|s| s.category == SinkCategory::SSRF));
    }

    #[test]
    fn test_rust_unsafe_sinks() {
        let registry = get_rust_sinks();

        let matches = registry.find_matches("std::mem::transmute(");
        assert!(!matches.is_empty());
        assert!(matches
            .iter()
            .any(|s| s.category == SinkCategory::MemoryCorruption));
        assert!(matches.iter().any(|s| s.severity() == 10));
    }

    #[test]
    fn test_sink_count() {
        let registry = get_rust_sinks();
        // Should have good coverage
        assert!(registry.len() > 60);
    }

    #[test]
    fn test_sink_categories_covered() {
        let registry = get_rust_sinks();
        let categories = registry.categories();

        // Should cover major categories
        assert!(categories.contains(&SinkCategory::SqlInjection));
        assert!(categories.contains(&SinkCategory::CommandInjection));
        assert!(categories.contains(&SinkCategory::PathTraversal));
        assert!(categories.contains(&SinkCategory::SSRF));
        assert!(categories.contains(&SinkCategory::MemoryCorruption));
    }
}
