//! Go-specific taint sink definitions.
//!
//! This module contains comprehensive sink definitions for Go security analysis,
//! covering standard library and popular frameworks:
//!
//! - **SQL**: database/sql, sqlx, gorm, ent
//! - **Web**: net/http, Gin, Echo, Fiber, Chi
//! - **Command**: os/exec
//! - **File**: os, io/ioutil, io/fs
//! - **Network**: net/http, net
//! - **Template**: html/template, text/template

use super::{Sink, SinkCategory, SinkRegistry};

/// Build the complete Go sink registry.
pub fn get_go_sinks() -> SinkRegistry {
    let mut registry = SinkRegistry::new();

    // Add all sink categories
    add_sql_sinks(&mut registry);
    add_command_sinks(&mut registry);
    add_path_sinks(&mut registry);
    add_xss_sinks(&mut registry);
    add_ssrf_sinks(&mut registry);
    add_deserialization_sinks(&mut registry);
    add_redirect_sinks(&mut registry);
    add_template_sinks(&mut registry);
    add_header_sinks(&mut registry);
    add_ldap_sinks(&mut registry);
    add_log_sinks(&mut registry);
    add_unsafe_sinks(&mut registry);

    registry
}

// =============================================================================
// SQL Injection Sinks
// =============================================================================

fn add_sql_sinks(registry: &mut SinkRegistry) {
    // database/sql standard library
    registry.add(Sink::sql("db.Query", "database/sql db.Query()"));
    registry.add(Sink::sql("db.QueryRow", "database/sql db.QueryRow()"));
    registry.add(Sink::sql("db.QueryContext", "database/sql db.QueryContext()"));
    registry.add(Sink::sql("db.QueryRowContext", "database/sql db.QueryRowContext()"));
    registry.add(Sink::sql("db.Exec", "database/sql db.Exec()"));
    registry.add(Sink::sql("db.ExecContext", "database/sql db.ExecContext()"));

    // Transaction methods
    registry.add(Sink::sql("tx.Query", "database/sql tx.Query()"));
    registry.add(Sink::sql("tx.QueryRow", "database/sql tx.QueryRow()"));
    registry.add(Sink::sql("tx.QueryContext", "database/sql tx.QueryContext()"));
    registry.add(Sink::sql("tx.QueryRowContext", "database/sql tx.QueryRowContext()"));
    registry.add(Sink::sql("tx.Exec", "database/sql tx.Exec()"));
    registry.add(Sink::sql("tx.ExecContext", "database/sql tx.ExecContext()"));

    // Prepared statements
    registry.add(Sink::sql("db.Prepare", "database/sql db.Prepare()"));
    registry.add(Sink::sql("db.PrepareContext", "database/sql db.PrepareContext()"));
    registry.add(Sink::sql("stmt.Query", "database/sql stmt.Query()"));
    registry.add(Sink::sql("stmt.QueryRow", "database/sql stmt.QueryRow()"));
    registry.add(Sink::sql("stmt.Exec", "database/sql stmt.Exec()"));

    // Connection methods
    registry.add(Sink::sql("conn.QueryContext", "database/sql conn.QueryContext()"));
    registry.add(Sink::sql("conn.ExecContext", "database/sql conn.ExecContext()"));

    // sqlx (popular extension)
    registry.add(Sink::sql("sqlx.Get", "sqlx Get()"));
    registry.add(Sink::sql("sqlx.Select", "sqlx Select()"));
    registry.add(Sink::sql("sqlx.Exec", "sqlx Exec()"));
    registry.add(Sink::sql("sqlx.Query", "sqlx Query()"));
    registry.add(Sink::sql("sqlx.QueryRow", "sqlx QueryRow()"));
    registry.add(Sink::sql("sqlx.NamedQuery", "sqlx NamedQuery()"));
    registry.add(Sink::sql("sqlx.NamedExec", "sqlx NamedExec()"));
    registry.add(Sink::sql("db.GetContext", "sqlx db.GetContext()"));
    registry.add(Sink::sql("db.SelectContext", "sqlx db.SelectContext()"));
    registry.add(Sink::sql("db.NamedExecContext", "sqlx db.NamedExecContext()"));

    // GORM
    registry.add(Sink::sql("db.Raw", "GORM db.Raw()").with_severity(9));
    registry.add(Sink::sql("db.Exec", "GORM db.Exec()"));
    registry.add(Sink::sql("db.Where", "GORM db.Where() (string form)").with_severity(7));
    registry.add(
        Sink::sql("db.Order", "GORM db.Order() (string form)").with_severity(6),
    );
    registry.add(
        Sink::sql("db.Group", "GORM db.Group() (string form)").with_severity(6),
    );
    registry.add(
        Sink::sql("db.Having", "GORM db.Having() (string form)").with_severity(7),
    );
    registry.add(
        Sink::sql("db.Joins", "GORM db.Joins() (string form)").with_severity(7),
    );

    // Ent ORM
    registry.add(Sink::sql("client.Exec", "Ent client.Exec()"));
    registry.add(Sink::sql("client.Query", "Ent client.Query()"));

    // pgx (PostgreSQL driver)
    registry.add(Sink::sql("conn.Query", "pgx conn.Query()"));
    registry.add(Sink::sql("conn.QueryRow", "pgx conn.QueryRow()"));
    registry.add(Sink::sql("conn.Exec", "pgx conn.Exec()"));
    registry.add(Sink::sql("pool.Query", "pgx pool.Query()"));
    registry.add(Sink::sql("pool.QueryRow", "pgx pool.QueryRow()"));
    registry.add(Sink::sql("pool.Exec", "pgx pool.Exec()"));
}

// =============================================================================
// Command Injection Sinks
// =============================================================================

fn add_command_sinks(registry: &mut SinkRegistry) {
    // os/exec package
    registry.add(Sink::command("exec.Command", "exec.Command()"));
    registry.add(Sink::command("exec.CommandContext", "exec.CommandContext()"));
    registry.add(Sink::command("cmd.Run", "cmd.Run()"));
    registry.add(Sink::command("cmd.Output", "cmd.Output()"));
    registry.add(Sink::command("cmd.CombinedOutput", "cmd.CombinedOutput()"));
    registry.add(Sink::command("cmd.Start", "cmd.Start()"));

    // os package process functions
    registry.add(Sink::command("os.StartProcess", "os.StartProcess()"));

    // syscall package
    registry.add(Sink::command("syscall.Exec", "syscall.Exec()").with_severity(10));
    registry.add(Sink::command("syscall.ForkExec", "syscall.ForkExec()").with_severity(10));
}

// =============================================================================
// Path Traversal Sinks
// =============================================================================

fn add_path_sinks(registry: &mut SinkRegistry) {
    // os package file operations
    registry.add(Sink::path("os.Open", "os.Open()"));
    registry.add(Sink::path("os.OpenFile", "os.OpenFile()"));
    registry.add(Sink::path("os.Create", "os.Create()"));
    registry.add(Sink::path("os.ReadFile", "os.ReadFile()"));
    registry.add(Sink::path("os.WriteFile", "os.WriteFile()"));
    registry.add(Sink::path("os.Remove", "os.Remove()"));
    registry.add(Sink::path("os.RemoveAll", "os.RemoveAll()").with_severity(9));
    registry.add(Sink::path("os.Rename", "os.Rename()"));
    registry.add(Sink::path("os.Mkdir", "os.Mkdir()"));
    registry.add(Sink::path("os.MkdirAll", "os.MkdirAll()"));
    registry.add(Sink::path("os.Chmod", "os.Chmod()"));
    registry.add(Sink::path("os.Chown", "os.Chown()"));
    registry.add(Sink::path("os.Link", "os.Link()"));
    registry.add(Sink::path("os.Symlink", "os.Symlink()"));
    registry.add(Sink::path("os.Readlink", "os.Readlink()"));
    registry.add(Sink::path("os.Stat", "os.Stat()"));
    registry.add(Sink::path("os.Lstat", "os.Lstat()"));
    registry.add(Sink::path("os.Truncate", "os.Truncate()"));

    // io/ioutil (deprecated but still used)
    registry.add(
        Sink::path("ioutil.ReadFile", "ioutil.ReadFile() (deprecated)")
            .with_tag("deprecated"),
    );
    registry.add(
        Sink::path("ioutil.WriteFile", "ioutil.WriteFile() (deprecated)")
            .with_tag("deprecated"),
    );
    registry.add(
        Sink::path("ioutil.ReadDir", "ioutil.ReadDir() (deprecated)")
            .with_tag("deprecated"),
    );

    // filepath package
    registry.add(
        Sink::path("filepath.Join", "filepath.Join() path construction")
            .with_severity(5),
    );
    registry.add(Sink::path("filepath.Clean", "filepath.Clean()").with_severity(4));
    registry.add(Sink::path("filepath.Abs", "filepath.Abs()").with_severity(4));

    // net/http file serving
    registry.add(
        Sink::path("http.ServeFile", "http.ServeFile()")
            .with_dangerous_params(vec![2]),
    );
    registry.add(Sink::path("http.FileServer", "http.FileServer()"));
    registry.add(Sink::path("http.Dir", "http.Dir()").with_severity(7));

    // Archive extraction
    registry.add(Sink::path("zip.OpenReader", "zip.OpenReader()").with_severity(7));
    registry.add(Sink::path("tar.NewReader", "tar.NewReader()").with_severity(7));
    registry.add(
        Sink::path("archive/zip", "zip extraction").with_severity(8),
    );
    registry.add(
        Sink::path("archive/tar", "tar extraction").with_severity(8),
    );

    // Gin static file serving
    registry.add(Sink::path("c.File", "Gin c.File()"));
    registry.add(Sink::path("r.Static", "Gin r.Static()"));
    registry.add(Sink::path("r.StaticFile", "Gin r.StaticFile()"));
    registry.add(Sink::path("r.StaticFS", "Gin r.StaticFS()"));

    // Echo static file serving
    registry.add(Sink::path("c.File", "Echo c.File()"));
    registry.add(Sink::path("e.Static", "Echo e.Static()"));
    registry.add(Sink::path("e.File", "Echo e.File()"));
}

// =============================================================================
// XSS Sinks
// =============================================================================

fn add_xss_sinks(registry: &mut SinkRegistry) {
    // template package unescaped output
    registry.add(Sink::xss("template.HTML", "template.HTML() unescaped").with_severity(8));
    registry.add(Sink::xss("template.JS", "template.JS() unescaped").with_severity(8));
    registry.add(Sink::xss("template.URL", "template.URL() unescaped").with_severity(7));
    registry.add(Sink::xss("template.CSS", "template.CSS() unescaped").with_severity(6));
    registry.add(Sink::xss("template.HTMLAttr", "template.HTMLAttr() unescaped").with_severity(7));

    // net/http response writing
    registry.add(Sink::xss("w.Write", "http.ResponseWriter.Write()").with_severity(5));
    registry.add(Sink::xss("w.WriteString", "WriteString() to response").with_severity(5));
    registry
        .add(Sink::xss("fmt.Fprintf(w", "fmt.Fprintf() to ResponseWriter").with_severity(5));
    registry.add(Sink::xss("fmt.Fprint(w", "fmt.Fprint() to ResponseWriter").with_severity(5));
    registry
        .add(Sink::xss("fmt.Fprintln(w", "fmt.Fprintln() to ResponseWriter").with_severity(5));
    registry.add(Sink::xss("io.WriteString(w", "io.WriteString() to response").with_severity(5));
    registry.add(Sink::xss("io.Copy(w", "io.Copy() to response").with_severity(5));

    // Gin framework
    registry.add(Sink::xss("c.String", "Gin c.String()").with_severity(5));
    registry.add(Sink::xss("c.HTML", "Gin c.HTML()").with_severity(4));
    registry.add(Sink::xss("c.Data", "Gin c.Data()").with_severity(6));
    registry.add(Sink::xss("c.Writer.Write", "Gin c.Writer.Write()").with_severity(5));

    // Echo framework
    registry.add(Sink::xss("c.String", "Echo c.String()").with_severity(5));
    registry.add(Sink::xss("c.HTML", "Echo c.HTML()").with_severity(4));
    registry.add(Sink::xss("c.HTMLBlob", "Echo c.HTMLBlob()").with_severity(6));

    // Fiber framework
    registry.add(Sink::xss("c.Send", "Fiber c.Send()").with_severity(5));
    registry.add(Sink::xss("c.SendString", "Fiber c.SendString()").with_severity(5));
}

// =============================================================================
// SSRF Sinks
// =============================================================================

fn add_ssrf_sinks(registry: &mut SinkRegistry) {
    // net/http client
    registry.add(Sink::ssrf("http.Get", "http.Get()"));
    registry.add(Sink::ssrf("http.Post", "http.Post()"));
    registry.add(Sink::ssrf("http.PostForm", "http.PostForm()"));
    registry.add(Sink::ssrf("http.Head", "http.Head()"));
    registry.add(Sink::ssrf("http.NewRequest", "http.NewRequest()"));
    registry.add(Sink::ssrf("http.NewRequestWithContext", "http.NewRequestWithContext()"));
    registry.add(Sink::ssrf("client.Do", "http.Client.Do()"));
    registry.add(Sink::ssrf("client.Get", "http.Client.Get()"));
    registry.add(Sink::ssrf("client.Post", "http.Client.Post()"));
    registry.add(Sink::ssrf("client.PostForm", "http.Client.PostForm()"));
    registry.add(Sink::ssrf("client.Head", "http.Client.Head()"));

    // net package
    registry.add(Sink::ssrf("net.Dial", "net.Dial()"));
    registry.add(Sink::ssrf("net.DialContext", "net.DialContext()"));
    registry.add(Sink::ssrf("net.DialTimeout", "net.DialTimeout()"));
    registry.add(Sink::ssrf("net.DialTCP", "net.DialTCP()"));
    registry.add(Sink::ssrf("net.DialUDP", "net.DialUDP()"));
    registry.add(Sink::ssrf("net.DialIP", "net.DialIP()"));
    registry.add(Sink::ssrf("net.DialUnix", "net.DialUnix()"));
    registry.add(Sink::ssrf("net.LookupHost", "net.LookupHost()").with_severity(5));
    registry.add(Sink::ssrf("net.LookupAddr", "net.LookupAddr()").with_severity(5));

    // resty client
    registry.add(Sink::ssrf("resty.R().Get", "resty R().Get()"));
    registry.add(Sink::ssrf("resty.R().Post", "resty R().Post()"));
    registry.add(Sink::ssrf("resty.R().SetURL", "resty R().SetURL()"));

    // grpc
    registry.add(Sink::ssrf("grpc.Dial", "grpc.Dial()"));
    registry.add(Sink::ssrf("grpc.DialContext", "grpc.DialContext()"));

    // WebSocket
    registry.add(Sink::ssrf("websocket.Dial", "websocket.Dial()").with_severity(6));
    registry.add(Sink::ssrf("websocket.DefaultDialer.Dial", "websocket DefaultDialer.Dial()"));
}

// =============================================================================
// Deserialization Sinks
// =============================================================================

fn add_deserialization_sinks(registry: &mut SinkRegistry) {
    // encoding/json (generally safe but included for completeness)
    registry.add(
        Sink::new("json.Unmarshal", SinkCategory::Deserialization)
            .with_severity(4),
    );
    registry.add(
        Sink::new("json.NewDecoder", SinkCategory::Deserialization)
            .with_severity(4),
    );
    registry.add(
        Sink::new("decoder.Decode", SinkCategory::Deserialization)
            .with_severity(4),
    );

    // encoding/xml (XXE possible depending on configuration)
    registry.add(
        Sink::new("xml.Unmarshal", SinkCategory::Deserialization)
            .with_severity(6),
    );
    registry.add(
        Sink::new("xml.NewDecoder", SinkCategory::Deserialization)
            .with_severity(6),
    );

    // encoding/gob (can be dangerous)
    registry.add(
        Sink::new("gob.NewDecoder", SinkCategory::Deserialization)
            .with_severity(7),
    );
    registry.add(
        Sink::new("gob.Decode", SinkCategory::Deserialization)
            .with_severity(7),
    );

    // yaml.v2/yaml.v3
    registry.add(
        Sink::new("yaml.Unmarshal", SinkCategory::Deserialization)
            .with_severity(6),
    );
    registry.add(
        Sink::new("yaml.NewDecoder", SinkCategory::Deserialization)
            .with_severity(6),
    );

    // msgpack
    registry.add(
        Sink::new("msgpack.Unmarshal", SinkCategory::Deserialization)
            .with_severity(5),
    );

    // protobuf
    registry.add(
        Sink::new("proto.Unmarshal", SinkCategory::Deserialization)
            .with_severity(4),
    );
}

// =============================================================================
// Open Redirect Sinks
// =============================================================================

fn add_redirect_sinks(registry: &mut SinkRegistry) {
    // net/http
    registry.add(
        Sink::new("http.Redirect", SinkCategory::OpenRedirect)
            .with_dangerous_params(vec![2]), // url parameter
    );

    // Gin
    registry.add(
        Sink::new("c.Redirect", SinkCategory::OpenRedirect)
            .with_dangerous_params(vec![1]),
    );

    // Echo
    registry.add(
        Sink::new("c.Redirect", SinkCategory::OpenRedirect)
            .with_dangerous_params(vec![1]),
    );

    // Fiber
    registry.add(
        Sink::new("c.Redirect", SinkCategory::OpenRedirect)
            .with_dangerous_params(vec![0]),
    );
}

// =============================================================================
// Template Injection Sinks
// =============================================================================

fn add_template_sinks(registry: &mut SinkRegistry) {
    // text/template (no auto-escaping - dangerous)
    registry.add(
        Sink::new("text/template.New", SinkCategory::TemplateInjection)
            .with_severity(8),
    );
    registry.add(
        Sink::new("text/template.Parse", SinkCategory::TemplateInjection)
            .with_severity(8),
    );
    registry.add(
        Sink::new("text/template.ParseFiles", SinkCategory::TemplateInjection)
            .with_severity(7),
    );
    registry.add(
        Sink::new("template.New", SinkCategory::TemplateInjection)
            .with_severity(7), // Could be either text or html
    );
    registry.add(
        Sink::new("template.Parse", SinkCategory::TemplateInjection)
            .with_severity(7),
    );
    registry.add(
        Sink::new("template.ParseFiles", SinkCategory::TemplateInjection)
            .with_severity(6),
    );
    registry.add(
        Sink::new("template.ParseGlob", SinkCategory::TemplateInjection)
            .with_severity(6),
    );

    // html/template (auto-escaping but still risky with user templates)
    registry.add(
        Sink::new("html/template.New", SinkCategory::TemplateInjection)
            .with_severity(6),
    );
    registry.add(
        Sink::new("html/template.Parse", SinkCategory::TemplateInjection)
            .with_severity(6),
    );
}

// =============================================================================
// HTTP Header Injection Sinks
// =============================================================================

fn add_header_sinks(registry: &mut SinkRegistry) {
    // net/http
    registry.add(Sink::header("w.Header().Set", "w.Header().Set()"));
    registry.add(Sink::header("w.Header().Add", "w.Header().Add()"));
    registry.add(Sink::header("http.SetCookie", "http.SetCookie()"));

    // Gin
    registry.add(Sink::header("c.Header", "Gin c.Header()"));
    registry.add(Sink::header("c.SetCookie", "Gin c.SetCookie()"));

    // Echo
    registry.add(Sink::header("c.Response().Header().Set", "Echo Header().Set()"));
}

// =============================================================================
// LDAP Injection Sinks
// =============================================================================

fn add_ldap_sinks(registry: &mut SinkRegistry) {
    // go-ldap
    registry.add(Sink::ldap("conn.Search", "ldap conn.Search()"));
    registry.add(Sink::ldap("conn.SearchWithPaging", "ldap conn.SearchWithPaging()"));
    registry.add(Sink::ldap("conn.Modify", "ldap conn.Modify()"));
    registry.add(Sink::ldap("conn.Add", "ldap conn.Add()"));
    registry.add(Sink::ldap("conn.Del", "ldap conn.Del()"));
    registry.add(Sink::ldap("ldap.NewSearchRequest", "ldap.NewSearchRequest()"));
}

// =============================================================================
// Log Injection Sinks
// =============================================================================

fn add_log_sinks(registry: &mut SinkRegistry) {
    // log package
    registry.add(Sink::log("log.Print", "log.Print()"));
    registry.add(Sink::log("log.Printf", "log.Printf()"));
    registry.add(Sink::log("log.Println", "log.Println()"));
    registry.add(Sink::log("log.Fatal", "log.Fatal()"));
    registry.add(Sink::log("log.Fatalf", "log.Fatalf()"));
    registry.add(Sink::log("log.Fatalln", "log.Fatalln()"));
    registry.add(Sink::log("log.Panic", "log.Panic()"));
    registry.add(Sink::log("log.Panicf", "log.Panicf()"));
    registry.add(Sink::log("log.Panicln", "log.Panicln()"));

    // Logger methods
    registry.add(Sink::log("logger.Print", "logger.Print()"));
    registry.add(Sink::log("logger.Printf", "logger.Printf()"));
    registry.add(Sink::log("logger.Println", "logger.Println()"));

    // zap logger
    registry.add(Sink::log("zap.S().Info", "zap S().Info()"));
    registry.add(Sink::log("zap.S().Error", "zap S().Error()"));
    registry.add(Sink::log("zap.L().Info", "zap L().Info()"));

    // logrus
    registry.add(Sink::log("logrus.Info", "logrus.Info()"));
    registry.add(Sink::log("logrus.Error", "logrus.Error()"));
    registry.add(Sink::log("logrus.WithFields", "logrus.WithFields()"));
}

// =============================================================================
// Unsafe/Memory Sinks
// =============================================================================

fn add_unsafe_sinks(registry: &mut SinkRegistry) {
    // unsafe package
    registry.add(
        Sink::new("unsafe.Pointer", SinkCategory::MemoryCorruption)
            .with_severity(9),
    );
    registry.add(
        Sink::new("unsafe.Slice", SinkCategory::MemoryCorruption)
            .with_severity(9),
    );
    registry.add(
        Sink::new("unsafe.SliceData", SinkCategory::MemoryCorruption)
            .with_severity(9),
    );
    registry.add(
        Sink::new("unsafe.String", SinkCategory::MemoryCorruption)
            .with_severity(9),
    );
    registry.add(
        Sink::new("unsafe.StringData", SinkCategory::MemoryCorruption)
            .with_severity(9),
    );

    // reflect package (can bypass type safety)
    registry.add(
        Sink::new("reflect.NewAt", SinkCategory::MemoryCorruption)
            .with_severity(7),
    );
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_go_sql_sinks() {
        let registry = get_go_sinks();

        let matches = registry.find_matches("db.Query");
        assert!(!matches.is_empty());
        assert!(matches
            .iter()
            .any(|s| s.category == SinkCategory::SqlInjection));
    }

    #[test]
    fn test_go_command_sinks() {
        let registry = get_go_sinks();

        let matches = registry.find_matches("exec.Command");
        assert!(!matches.is_empty());
        assert!(matches
            .iter()
            .any(|s| s.category == SinkCategory::CommandInjection));
    }

    #[test]
    fn test_go_path_sinks() {
        let registry = get_go_sinks();

        let matches = registry.find_matches("os.Open");
        assert!(!matches.is_empty());
        assert!(matches
            .iter()
            .any(|s| s.category == SinkCategory::PathTraversal));
    }

    #[test]
    fn test_go_xss_sinks() {
        let registry = get_go_sinks();

        let matches = registry.find_matches("template.HTML");
        assert!(!matches.is_empty());
        assert!(matches.iter().any(|s| s.category == SinkCategory::XSS));
    }

    #[test]
    fn test_go_ssrf_sinks() {
        let registry = get_go_sinks();

        let matches = registry.find_matches("http.Get");
        assert!(!matches.is_empty());
        assert!(matches.iter().any(|s| s.category == SinkCategory::SSRF));
    }

    #[test]
    fn test_sink_count() {
        let registry = get_go_sinks();
        // Should have comprehensive coverage
        assert!(registry.len() > 80);
    }

    #[test]
    fn test_sink_categories_covered() {
        let registry = get_go_sinks();
        let categories = registry.categories();

        // Should cover major categories
        assert!(categories.contains(&SinkCategory::SqlInjection));
        assert!(categories.contains(&SinkCategory::CommandInjection));
        assert!(categories.contains(&SinkCategory::XSS));
        assert!(categories.contains(&SinkCategory::PathTraversal));
        assert!(categories.contains(&SinkCategory::SSRF));
    }
}
