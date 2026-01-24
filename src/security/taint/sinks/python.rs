//! Python-specific taint sink definitions.
//!
//! This module contains comprehensive sink definitions for Python security analysis,
//! covering major frameworks and libraries:
//!
//! - **SQL**: sqlite3, psycopg2, MySQLdb, SQLAlchemy, Django ORM
//! - **Web**: Flask, Django, FastAPI, aiohttp
//! - **Command**: os, subprocess, commands
//! - **File**: open, pathlib, shutil
//! - **Network**: requests, urllib, httpx, aiohttp
//! - **Deserialization**: pickle, yaml, marshal

use super::{SanitizerContext, Sink, SinkCategory, SinkRegistry};

/// Build the complete Python sink registry.
pub fn get_python_sinks() -> SinkRegistry {
    let mut registry = SinkRegistry::new();

    // Add all sink categories
    add_sql_sinks(&mut registry);
    add_command_sinks(&mut registry);
    add_code_execution_sinks(&mut registry);
    add_path_sinks(&mut registry);
    add_xss_sinks(&mut registry);
    add_ssrf_sinks(&mut registry);
    add_deserialization_sinks(&mut registry);
    add_ldap_sinks(&mut registry);
    add_xpath_sinks(&mut registry);
    add_xml_sinks(&mut registry);
    add_redirect_sinks(&mut registry);
    add_template_sinks(&mut registry);
    add_log_sinks(&mut registry);
    add_header_sinks(&mut registry);
    add_email_sinks(&mut registry);
    add_nosql_sinks(&mut registry);
    add_regex_sinks(&mut registry);

    registry
}

// =============================================================================
// SQL Injection Sinks
// =============================================================================

fn add_sql_sinks(registry: &mut SinkRegistry) {
    // Standard library sqlite3
    registry.add(Sink::sql("cursor.execute", "SQLite cursor execute"));
    registry.add(Sink::sql("cursor.executemany", "SQLite cursor executemany"));
    registry
        .add(Sink::sql("cursor.executescript", "SQLite cursor executescript").with_severity(10)); // executescript is especially dangerous
    registry.add(Sink::sql("connection.execute", "SQLite connection execute"));
    registry.add(Sink::sql("conn.execute", "SQLite connection execute"));

    // psycopg2 (PostgreSQL)
    registry.add(Sink::sql("cursor.execute", "psycopg2 cursor execute"));
    registry.add(Sink::sql(
        "cursor.executemany",
        "psycopg2 cursor executemany",
    ));
    registry.add(Sink::sql("cursor.copy_from", "psycopg2 COPY FROM"));
    registry.add(Sink::sql("cursor.copy_to", "psycopg2 COPY TO"));
    registry.add(Sink::sql("cursor.copy_expert", "psycopg2 COPY EXPERT").with_severity(10));

    // asyncpg (PostgreSQL async)
    registry.add(Sink::sql("connection.execute", "asyncpg execute"));
    registry.add(Sink::sql("connection.fetch", "asyncpg fetch"));
    registry.add(Sink::sql("connection.fetchrow", "asyncpg fetchrow"));
    registry.add(Sink::sql("connection.fetchval", "asyncpg fetchval"));
    registry.add(Sink::sql("pool.execute", "asyncpg pool execute"));
    registry.add(Sink::sql("pool.fetch", "asyncpg pool fetch"));

    // MySQLdb / mysql-connector-python
    registry.add(Sink::sql("cursor.execute", "MySQL cursor execute"));
    registry.add(Sink::sql("cursor.executemany", "MySQL cursor executemany"));

    // aiomysql (MySQL async)
    registry.add(Sink::sql("cursor.execute", "aiomysql cursor execute"));

    // SQLAlchemy
    registry.add(Sink::sql("engine.execute", "SQLAlchemy engine execute"));
    registry.add(Sink::sql(
        "connection.execute",
        "SQLAlchemy connection execute",
    ));
    registry.add(Sink::sql("session.execute", "SQLAlchemy session execute"));
    registry.add(Sink::sql("text(", "SQLAlchemy text() raw SQL").with_dangerous_params(vec![0]));
    registry.add(Sink::sql("TextClause", "SQLAlchemy TextClause"));

    // Django ORM
    registry.add(Sink::sql(".raw(", "Django ORM raw() query").with_severity(9));
    registry.add(
        Sink::sql(".extra(", "Django ORM extra() (deprecated)")
            .with_severity(8)
            .with_tag("deprecated"),
    );
    registry.add(Sink::sql("RawSQL(", "Django RawSQL expression"));
    registry.add(Sink::sql(
        "connection.cursor().execute",
        "Django raw cursor execute",
    ));

    // Peewee ORM
    registry.add(Sink::sql("database.execute_sql", "Peewee execute_sql"));
    registry.add(Sink::sql("SQL(", "Peewee SQL() expression"));

    // aiosqlite
    registry.add(Sink::sql("db.execute", "aiosqlite execute"));
    registry.add(Sink::sql("db.executemany", "aiosqlite executemany"));
    registry.add(Sink::sql("db.executescript", "aiosqlite executescript"));
}

// =============================================================================
// Command Injection Sinks
// =============================================================================

fn add_command_sinks(registry: &mut SinkRegistry) {
    // os module
    registry.add(Sink::command("os.system", "os.system() shell command").with_severity(10));
    registry.add(Sink::command("os.popen", "os.popen() shell command").with_severity(10));
    registry.add(Sink::command("os.popen2", "os.popen2() shell command").with_severity(10));
    registry.add(Sink::command("os.popen3", "os.popen3() shell command").with_severity(10));
    registry.add(Sink::command("os.popen4", "os.popen4() shell command").with_severity(10));
    registry.add(Sink::command("os.spawn", "os.spawn*() process spawn"));
    registry.add(Sink::command("os.spawnl", "os.spawnl() process spawn"));
    registry.add(Sink::command("os.spawnle", "os.spawnle() process spawn"));
    registry.add(Sink::command("os.spawnlp", "os.spawnlp() process spawn"));
    registry.add(Sink::command("os.spawnlpe", "os.spawnlpe() process spawn"));
    registry.add(Sink::command("os.spawnv", "os.spawnv() process spawn"));
    registry.add(Sink::command("os.spawnve", "os.spawnve() process spawn"));
    registry.add(Sink::command("os.spawnvp", "os.spawnvp() process spawn"));
    registry.add(Sink::command("os.spawnvpe", "os.spawnvpe() process spawn"));
    registry.add(Sink::command("os.execl", "os.exec*() replace process"));
    registry.add(Sink::command("os.execle", "os.execle() replace process"));
    registry.add(Sink::command("os.execlp", "os.execlp() replace process"));
    registry.add(Sink::command("os.execlpe", "os.execlpe() replace process"));
    registry.add(Sink::command("os.execv", "os.execv() replace process"));
    registry.add(Sink::command("os.execve", "os.execve() replace process"));
    registry.add(Sink::command("os.execvp", "os.execvp() replace process"));
    registry.add(Sink::command("os.execvpe", "os.execvpe() replace process"));

    // subprocess module
    registry
        .add(Sink::command("subprocess.call", "subprocess.call()").with_dangerous_params(vec![0]));
    registry
        .add(Sink::command("subprocess.run", "subprocess.run()").with_dangerous_params(vec![0]));
    registry.add(
        Sink::command("subprocess.Popen", "subprocess.Popen()").with_dangerous_params(vec![0]),
    );
    registry.add(
        Sink::command("subprocess.check_call", "subprocess.check_call()")
            .with_dangerous_params(vec![0]),
    );
    registry.add(
        Sink::command("subprocess.check_output", "subprocess.check_output()")
            .with_dangerous_params(vec![0]),
    );
    registry.add(Sink::command("subprocess.getoutput", "subprocess.getoutput()").with_severity(10));
    registry.add(
        Sink::command("subprocess.getstatusoutput", "subprocess.getstatusoutput()")
            .with_severity(10),
    );

    // asyncio subprocess
    registry.add(
        Sink::command(
            "asyncio.create_subprocess_shell",
            "asyncio shell subprocess",
        )
        .with_severity(10),
    );
    registry.add(Sink::command(
        "asyncio.create_subprocess_exec",
        "asyncio exec subprocess",
    ));

    // Deprecated commands module (Python 2)
    registry.add(
        Sink::command("commands.getoutput", "commands.getoutput() (deprecated)")
            .with_severity(10)
            .with_tag("deprecated"),
    );
    registry.add(
        Sink::command(
            "commands.getstatusoutput",
            "commands.getstatusoutput() (deprecated)",
        )
        .with_severity(10)
        .with_tag("deprecated"),
    );

    // pty module
    registry.add(Sink::command("pty.spawn", "pty.spawn() terminal spawn").with_severity(10));

    // pexpect
    registry.add(Sink::command("pexpect.spawn", "pexpect.spawn()"));
    registry.add(Sink::command("pexpect.run", "pexpect.run()"));

    // fabric
    registry.add(Sink::command("fabric.run", "fabric run() remote command"));
    registry.add(Sink::command("fabric.local", "fabric local() command"));
    registry.add(Sink::command("fabric.sudo", "fabric sudo() command"));
}

// =============================================================================
// Code Execution Sinks
// =============================================================================

fn add_code_execution_sinks(registry: &mut SinkRegistry) {
    // Built-in dangerous functions
    registry.add(Sink::code_exec("eval(", "eval() code execution").with_severity(10));
    registry.add(Sink::code_exec("exec(", "exec() code execution").with_severity(10));
    registry.add(Sink::code_exec("compile(", "compile() code compilation").with_severity(9));
    registry.add(Sink::code_exec("__import__(", "Dynamic import").with_severity(8));
    registry
        .add(Sink::code_exec("importlib.import_module", "Dynamic module import").with_severity(8));

    // Code object manipulation
    registry
        .add(Sink::code_exec("types.FunctionType", "Dynamic function creation").with_severity(9));
    registry.add(Sink::code_exec("types.CodeType", "Code object creation").with_severity(9));

    // AST-based code execution
    registry.add(
        Sink::code_exec("ast.literal_eval", "ast.literal_eval() (safer but limited)")
            .with_severity(4),
    );
}

// =============================================================================
// Path Traversal Sinks
// =============================================================================

fn add_path_sinks(registry: &mut SinkRegistry) {
    // Built-in open
    registry.add(Sink::path("open(", "open() file access").with_dangerous_params(vec![0]));

    // os module file operations
    registry.add(Sink::path("os.open", "os.open() file open"));
    registry.add(Sink::path("os.fdopen", "os.fdopen() file descriptor open"));
    registry.add(Sink::path("os.path.join", "os.path.join() path construction").with_severity(5)); // Less dangerous if used correctly
    registry.add(Sink::path("os.remove", "os.remove() file deletion"));
    registry.add(Sink::path("os.unlink", "os.unlink() file deletion"));
    registry.add(Sink::path("os.rename", "os.rename() file rename"));
    registry.add(Sink::path("os.renames", "os.renames() recursive rename"));
    registry.add(Sink::path("os.replace", "os.replace() file replace"));
    registry.add(Sink::path("os.mkdir", "os.mkdir() directory creation"));
    registry.add(Sink::path(
        "os.makedirs",
        "os.makedirs() recursive directory creation",
    ));
    registry.add(Sink::path("os.rmdir", "os.rmdir() directory removal"));
    registry.add(Sink::path(
        "os.removedirs",
        "os.removedirs() recursive directory removal",
    ));
    registry.add(Sink::path("os.listdir", "os.listdir() directory listing"));
    registry.add(Sink::path("os.scandir", "os.scandir() directory scan"));
    registry.add(Sink::path("os.walk", "os.walk() directory tree walk"));
    registry.add(Sink::path("os.chdir", "os.chdir() change directory"));
    registry.add(Sink::path("os.chroot", "os.chroot() change root"));
    registry.add(Sink::path("os.chmod", "os.chmod() change permissions"));
    registry.add(Sink::path("os.chown", "os.chown() change ownership"));
    registry.add(Sink::path("os.link", "os.link() hard link creation"));
    registry.add(Sink::path(
        "os.symlink",
        "os.symlink() symbolic link creation",
    ));
    registry.add(Sink::path(
        "os.readlink",
        "os.readlink() read symbolic link",
    ));
    registry.add(Sink::path("os.stat", "os.stat() file status"));
    registry.add(Sink::path("os.lstat", "os.lstat() symbolic link status"));
    registry.add(Sink::path("os.access", "os.access() file access check"));
    registry.add(Sink::path("os.truncate", "os.truncate() file truncation"));

    // pathlib module
    registry.add(Sink::path("pathlib.Path", "pathlib.Path() construction").with_severity(5));
    registry.add(Sink::path("Path(", "pathlib.Path() construction").with_severity(5));
    registry.add(Sink::path(".read_text(", "pathlib read_text()"));
    registry.add(Sink::path(".read_bytes(", "pathlib read_bytes()"));
    registry.add(Sink::path(".write_text(", "pathlib write_text()"));
    registry.add(Sink::path(".write_bytes(", "pathlib write_bytes()"));
    registry.add(Sink::path(".open(", "pathlib open()"));
    registry.add(Sink::path(".unlink(", "pathlib unlink()"));
    registry.add(Sink::path(".rmdir(", "pathlib rmdir()"));
    registry.add(Sink::path(".mkdir(", "pathlib mkdir()"));

    // shutil module
    registry.add(Sink::path("shutil.copy", "shutil.copy() file copy"));
    registry.add(Sink::path(
        "shutil.copy2",
        "shutil.copy2() file copy with metadata",
    ));
    registry.add(Sink::path(
        "shutil.copyfile",
        "shutil.copyfile() content copy",
    ));
    registry.add(Sink::path(
        "shutil.copytree",
        "shutil.copytree() directory copy",
    ));
    registry.add(Sink::path("shutil.move", "shutil.move() file/dir move"));
    registry.add(Sink::path("shutil.rmtree", "shutil.rmtree() recursive delete").with_severity(9));
    registry.add(Sink::path(
        "shutil.chown",
        "shutil.chown() ownership change",
    ));
    registry.add(Sink::path(
        "shutil.make_archive",
        "shutil.make_archive() archive creation",
    ));
    registry.add(
        Sink::path(
            "shutil.unpack_archive",
            "shutil.unpack_archive() archive extraction",
        )
        .with_severity(9),
    ); // Zip slip vulnerability

    // io module
    registry.add(Sink::path("io.open", "io.open() file open"));
    registry.add(Sink::path("io.FileIO", "io.FileIO() file I/O"));

    // aiofiles (async file I/O)
    registry.add(Sink::path(
        "aiofiles.open",
        "aiofiles.open() async file open",
    ));

    // tarfile/zipfile (archive extraction)
    registry.add(Sink::path("tarfile.open", "tarfile.open() tar archive").with_severity(8));
    registry.add(Sink::path("zipfile.ZipFile", "zipfile.ZipFile() zip archive").with_severity(8));
    registry.add(Sink::path(".extract(", "Archive extract()").with_severity(9)); // Zip slip
    registry.add(Sink::path(".extractall(", "Archive extractall()").with_severity(9));
    // Zip slip
}

// =============================================================================
// XSS Sinks
// =============================================================================

fn add_xss_sinks(registry: &mut SinkRegistry) {
    // Flask/Jinja2
    registry.add(Sink::xss("Markup(", "Flask Markup() unescaped HTML").with_severity(8));
    registry.add(
        Sink::xss(
            "render_template_string",
            "Jinja2 render_template_string() SSTI risk",
        )
        .with_severity(9),
    );
    registry.add(Sink::xss("jinja2.Template", "Direct Jinja2 Template()"));
    registry.add(Sink::xss("make_response", "Flask make_response()").with_severity(5));
    registry.add(Sink::xss("Response(", "Direct Response() creation").with_severity(5));
    registry.add(Sink::xss("jsonify", "Flask jsonify() (usually safe)").with_severity(3));

    // Django
    registry.add(Sink::xss("mark_safe", "Django mark_safe() unescaped HTML").with_severity(8));
    registry.add(Sink::xss("SafeString", "Django SafeString() unescaped HTML").with_severity(8));
    registry
        .add(Sink::xss("format_html", "Django format_html() (partially safe)").with_severity(4));
    registry.add(Sink::xss("HttpResponse(", "Django HttpResponse()").with_severity(5));

    // FastAPI/Starlette
    registry.add(Sink::xss("HTMLResponse", "FastAPI HTMLResponse()").with_severity(6));
    registry.add(Sink::xss("Response(", "Starlette Response()").with_severity(5));
}

// =============================================================================
// SSRF Sinks
// =============================================================================

fn add_ssrf_sinks(registry: &mut SinkRegistry) {
    // requests library
    registry.add(Sink::ssrf("requests.get", "requests.get() HTTP GET"));
    registry.add(Sink::ssrf("requests.post", "requests.post() HTTP POST"));
    registry.add(Sink::ssrf("requests.put", "requests.put() HTTP PUT"));
    registry.add(Sink::ssrf(
        "requests.delete",
        "requests.delete() HTTP DELETE",
    ));
    registry.add(Sink::ssrf("requests.patch", "requests.patch() HTTP PATCH"));
    registry.add(Sink::ssrf("requests.head", "requests.head() HTTP HEAD"));
    registry.add(Sink::ssrf(
        "requests.options",
        "requests.options() HTTP OPTIONS",
    ));
    registry.add(Sink::ssrf(
        "requests.request",
        "requests.request() generic HTTP",
    ));
    registry.add(Sink::ssrf("Session.get", "requests Session.get()"));
    registry.add(Sink::ssrf("Session.post", "requests Session.post()"));
    registry.add(Sink::ssrf("Session.request", "requests Session.request()"));

    // urllib
    registry.add(Sink::ssrf(
        "urllib.request.urlopen",
        "urllib.request.urlopen()",
    ));
    registry.add(Sink::ssrf(
        "urllib.request.Request",
        "urllib.request.Request()",
    ));
    registry.add(Sink::ssrf(
        "urllib.request.urlretrieve",
        "urllib.request.urlretrieve()",
    ));
    registry
        .add(Sink::ssrf("urllib2.urlopen", "urllib2.urlopen() (Python 2)").with_tag("deprecated"));
    registry
        .add(Sink::ssrf("urllib2.Request", "urllib2.Request() (Python 2)").with_tag("deprecated"));

    // httpx (async HTTP client)
    registry.add(Sink::ssrf("httpx.get", "httpx.get()"));
    registry.add(Sink::ssrf("httpx.post", "httpx.post()"));
    registry.add(Sink::ssrf("httpx.request", "httpx.request()"));
    registry.add(Sink::ssrf("httpx.AsyncClient", "httpx AsyncClient()"));
    registry.add(Sink::ssrf("AsyncClient.get", "httpx AsyncClient.get()"));
    registry.add(Sink::ssrf("AsyncClient.post", "httpx AsyncClient.post()"));

    // aiohttp
    registry.add(Sink::ssrf(
        "aiohttp.ClientSession",
        "aiohttp ClientSession()",
    ));
    registry.add(Sink::ssrf(
        "ClientSession.get",
        "aiohttp ClientSession.get()",
    ));
    registry.add(Sink::ssrf(
        "ClientSession.post",
        "aiohttp ClientSession.post()",
    ));
    registry.add(Sink::ssrf(
        "ClientSession.request",
        "aiohttp ClientSession.request()",
    ));

    // http.client
    registry.add(Sink::ssrf(
        "http.client.HTTPConnection",
        "http.client HTTPConnection()",
    ));
    registry.add(Sink::ssrf(
        "http.client.HTTPSConnection",
        "http.client HTTPSConnection()",
    ));
    registry.add(Sink::ssrf(
        "HTTPConnection.request",
        "HTTPConnection.request()",
    ));

    // pycurl
    registry.add(Sink::ssrf("pycurl.Curl", "pycurl Curl()"));
    registry.add(Sink::ssrf("Curl.setopt", "pycurl setopt() URL setting"));
}

// =============================================================================
// Deserialization Sinks
// =============================================================================

fn add_deserialization_sinks(registry: &mut SinkRegistry) {
    // pickle (extremely dangerous)
    registry.add(
        Sink::new("pickle.loads", SinkCategory::Deserialization)
            .with_severity(10)
            .with_sanitizers(vec![
                SanitizerContext::DeserializeSignatureVerify,
                SanitizerContext::InputAllowlist,
            ]),
    );
    registry.add(Sink::new("pickle.load", SinkCategory::Deserialization).with_severity(10));
    registry.add(Sink::new("pickle.Unpickler", SinkCategory::Deserialization).with_severity(10));
    registry.add(
        Sink::new("cPickle.loads", SinkCategory::Deserialization)
            .with_severity(10)
            .with_tag("deprecated"),
    );
    registry.add(
        Sink::new("cPickle.load", SinkCategory::Deserialization)
            .with_severity(10)
            .with_tag("deprecated"),
    );

    // yaml (unsafe by default)
    registry.add(
        Sink::new("yaml.load", SinkCategory::Deserialization)
            .with_severity(9)
            .with_sanitizers(vec![SanitizerContext::DeserializeSafeFormat]),
    );
    registry.add(Sink::new("yaml.unsafe_load", SinkCategory::Deserialization).with_severity(10));
    registry.add(Sink::new("yaml.full_load", SinkCategory::Deserialization).with_severity(8));
    // yaml.safe_load is safe, not added as sink

    // marshal (dangerous)
    registry.add(Sink::new("marshal.loads", SinkCategory::Deserialization).with_severity(9));
    registry.add(Sink::new("marshal.load", SinkCategory::Deserialization).with_severity(9));

    // shelve (uses pickle internally)
    registry.add(Sink::new("shelve.open", SinkCategory::Deserialization).with_severity(8));

    // dill (pickle extension)
    registry.add(Sink::new("dill.loads", SinkCategory::Deserialization).with_severity(10));
    registry.add(Sink::new("dill.load", SinkCategory::Deserialization).with_severity(10));

    // jsonpickle
    registry.add(Sink::new("jsonpickle.decode", SinkCategory::Deserialization).with_severity(9));

    // cloudpickle
    registry.add(Sink::new("cloudpickle.loads", SinkCategory::Deserialization).with_severity(10));
}

// =============================================================================
// LDAP Injection Sinks
// =============================================================================

fn add_ldap_sinks(registry: &mut SinkRegistry) {
    // python-ldap
    registry.add(Sink::ldap("ldap.search_s", "python-ldap search_s()"));
    registry.add(Sink::ldap("ldap.search", "python-ldap search()"));
    registry.add(Sink::ldap("ldap.search_ext", "python-ldap search_ext()"));
    registry.add(Sink::ldap(
        "ldap.search_ext_s",
        "python-ldap search_ext_s()",
    ));
    registry.add(Sink::ldap("ldap.modify_s", "python-ldap modify_s()"));
    registry.add(Sink::ldap("ldap.add_s", "python-ldap add_s()"));
    registry.add(Sink::ldap("ldap.delete_s", "python-ldap delete_s()"));

    // ldap3
    registry.add(Sink::ldap("connection.search", "ldap3 connection.search()"));
    registry.add(Sink::ldap("connection.add", "ldap3 connection.add()"));
    registry.add(Sink::ldap("connection.modify", "ldap3 connection.modify()"));
    registry.add(Sink::ldap("connection.delete", "ldap3 connection.delete()"));
}

// =============================================================================
// XPath Injection Sinks
// =============================================================================

fn add_xpath_sinks(registry: &mut SinkRegistry) {
    // lxml
    registry.add(Sink::xpath("etree.XPath", "lxml etree.XPath()"));
    registry.add(Sink::xpath(".xpath(", "lxml xpath() method"));

    // xml.etree.ElementTree
    registry.add(Sink::xpath("ElementTree.find", "ElementTree find()"));
    registry.add(Sink::xpath("ElementTree.findall", "ElementTree findall()"));
    registry.add(Sink::xpath(
        "ElementTree.findtext",
        "ElementTree findtext()",
    ));
    registry.add(Sink::xpath("Element.find", "Element find()"));
    registry.add(Sink::xpath("Element.findall", "Element findall()"));
}

// =============================================================================
// XML Injection (XXE) Sinks
// =============================================================================

fn add_xml_sinks(registry: &mut SinkRegistry) {
    // xml.etree.ElementTree (has XXE by default in older Python)
    registry.add(
        Sink::new("xml.etree.ElementTree.parse", SinkCategory::XmlInjection)
            .with_severity(7)
            .with_sanitizers(vec![SanitizerContext::XmlDisableExternalEntities]),
    );
    registry.add(
        Sink::new(
            "xml.etree.ElementTree.fromstring",
            SinkCategory::XmlInjection,
        )
        .with_severity(7),
    );
    registry.add(Sink::new("ElementTree.parse", SinkCategory::XmlInjection).with_severity(7));
    registry.add(Sink::new("ET.parse", SinkCategory::XmlInjection).with_severity(7));
    registry.add(Sink::new("ET.fromstring", SinkCategory::XmlInjection).with_severity(7));

    // lxml (safe by default but can be configured unsafely)
    registry.add(Sink::new("lxml.etree.parse", SinkCategory::XmlInjection).with_severity(6));
    registry.add(Sink::new("lxml.etree.fromstring", SinkCategory::XmlInjection).with_severity(6));
    registry.add(Sink::new("lxml.etree.XML", SinkCategory::XmlInjection).with_severity(6));

    // xml.dom.minidom
    registry.add(Sink::new("xml.dom.minidom.parse", SinkCategory::XmlInjection).with_severity(8));
    registry
        .add(Sink::new("xml.dom.minidom.parseString", SinkCategory::XmlInjection).with_severity(8));

    // xml.sax (vulnerable)
    registry.add(Sink::new("xml.sax.parse", SinkCategory::XmlInjection).with_severity(8));
    registry.add(Sink::new("xml.sax.parseString", SinkCategory::XmlInjection).with_severity(8));
}

// =============================================================================
// Open Redirect Sinks
// =============================================================================

fn add_redirect_sinks(registry: &mut SinkRegistry) {
    // Flask
    registry.add(Sink::new("redirect(", SinkCategory::OpenRedirect).with_dangerous_params(vec![0]));
    registry.add(
        Sink::new("flask.redirect", SinkCategory::OpenRedirect).with_dangerous_params(vec![0]),
    );

    // Django
    registry.add(
        Sink::new("HttpResponseRedirect", SinkCategory::OpenRedirect)
            .with_dangerous_params(vec![0]),
    );
    registry.add(
        Sink::new("HttpResponsePermanentRedirect", SinkCategory::OpenRedirect)
            .with_dangerous_params(vec![0]),
    );
    registry.add(Sink::new("redirect(", SinkCategory::OpenRedirect).with_dangerous_params(vec![0]));

    // FastAPI/Starlette
    registry.add(
        Sink::new("RedirectResponse", SinkCategory::OpenRedirect).with_dangerous_params(vec![0]),
    );
}

// =============================================================================
// Template Injection (SSTI) Sinks
// =============================================================================

fn add_template_sinks(registry: &mut SinkRegistry) {
    // Jinja2
    registry.add(Sink::new("jinja2.Template", SinkCategory::TemplateInjection).with_severity(9));
    registry.add(Sink::new("Template(", SinkCategory::TemplateInjection).with_severity(9));
    registry.add(
        Sink::new("Environment.from_string", SinkCategory::TemplateInjection).with_severity(9),
    );

    // Mako
    registry
        .add(Sink::new("mako.template.Template", SinkCategory::TemplateInjection).with_severity(9));

    // string.Template (limited injection risk)
    registry.add(Sink::new("string.Template", SinkCategory::TemplateInjection).with_severity(4));

    // Django templates
    registry.add(
        Sink::new("django.template.Template", SinkCategory::TemplateInjection).with_severity(6), // Django templates are sandboxed
    );

    // Tornado templates
    registry.add(
        Sink::new("tornado.template.Template", SinkCategory::TemplateInjection).with_severity(8),
    );
}

// =============================================================================
// Log Injection Sinks
// =============================================================================

fn add_log_sinks(registry: &mut SinkRegistry) {
    // logging module
    registry.add(Sink::log("logging.debug", "logging.debug()"));
    registry.add(Sink::log("logging.info", "logging.info()"));
    registry.add(Sink::log("logging.warning", "logging.warning()"));
    registry.add(Sink::log("logging.error", "logging.error()"));
    registry.add(Sink::log("logging.critical", "logging.critical()"));
    registry.add(Sink::log("logging.exception", "logging.exception()"));
    registry.add(Sink::log("logging.log", "logging.log()"));
    registry.add(Sink::log("logger.debug", "logger.debug()"));
    registry.add(Sink::log("logger.info", "logger.info()"));
    registry.add(Sink::log("logger.warning", "logger.warning()"));
    registry.add(Sink::log("logger.error", "logger.error()"));
    registry.add(Sink::log("logger.critical", "logger.critical()"));
    registry.add(Sink::log("logger.exception", "logger.exception()"));

    // print (lower severity)
    registry.add(Sink::log("print(", "print() to stdout").with_severity(2));
}

// =============================================================================
// HTTP Header Injection Sinks
// =============================================================================

fn add_header_sinks(registry: &mut SinkRegistry) {
    // Flask
    registry.add(Sink::header(
        "response.headers[",
        "Flask response header setting",
    ));
    registry.add(Sink::header(
        "make_response",
        "Flask make_response() with headers",
    ));

    // Django
    registry.add(Sink::header("response[", "Django response header setting"));

    // Generic
    registry.add(Sink::header("add_header", "Generic add_header()"));
    registry.add(Sink::header("set_header", "Generic set_header()"));
}

// =============================================================================
// Email Header Injection Sinks
// =============================================================================

fn add_email_sinks(registry: &mut SinkRegistry) {
    // smtplib
    registry.add(
        Sink::new("smtplib.sendmail", SinkCategory::EmailHeaderInjection)
            .with_dangerous_params(vec![0, 1]), // from_addr, to_addrs
    );
    registry.add(Sink::new(
        "smtplib.send_message",
        SinkCategory::EmailHeaderInjection,
    ));

    // email.message
    registry.add(Sink::new(
        "email.message.Message",
        SinkCategory::EmailHeaderInjection,
    ));
    registry.add(Sink::new("email.mime", SinkCategory::EmailHeaderInjection).with_severity(5));

    // Django mail
    registry.add(Sink::new(
        "django.core.mail.send_mail",
        SinkCategory::EmailHeaderInjection,
    ));
    registry.add(Sink::new(
        "django.core.mail.EmailMessage",
        SinkCategory::EmailHeaderInjection,
    ));
}

// =============================================================================
// NoSQL Injection Sinks
// =============================================================================

fn add_nosql_sinks(registry: &mut SinkRegistry) {
    // pymongo (MongoDB)
    registry.add(
        Sink::new("collection.find", SinkCategory::NoSqlInjection).with_dangerous_params(vec![0]), // query filter
    );
    registry.add(
        Sink::new("collection.find_one", SinkCategory::NoSqlInjection)
            .with_dangerous_params(vec![0]),
    );
    registry.add(
        Sink::new("collection.update_one", SinkCategory::NoSqlInjection)
            .with_dangerous_params(vec![0, 1]),
    );
    registry.add(
        Sink::new("collection.update_many", SinkCategory::NoSqlInjection)
            .with_dangerous_params(vec![0, 1]),
    );
    registry.add(
        Sink::new("collection.delete_one", SinkCategory::NoSqlInjection)
            .with_dangerous_params(vec![0]),
    );
    registry.add(
        Sink::new("collection.delete_many", SinkCategory::NoSqlInjection)
            .with_dangerous_params(vec![0]),
    );
    registry.add(
        Sink::new("collection.aggregate", SinkCategory::NoSqlInjection)
            .with_dangerous_params(vec![0]),
    );

    // motor (async MongoDB)
    registry
        .add(Sink::new("motor.find", SinkCategory::NoSqlInjection).with_dangerous_params(vec![0]));

    // redis (command injection possible)
    registry.add(Sink::new("redis.execute_command", SinkCategory::NoSqlInjection).with_severity(8));
    registry.add(
        Sink::new("redis.eval", SinkCategory::NoSqlInjection).with_severity(9), // Lua script execution
    );
}

// =============================================================================
// Regular Expression Injection Sinks
// =============================================================================

fn add_regex_sinks(registry: &mut SinkRegistry) {
    // re module
    registry.add(
        Sink::new("re.compile", SinkCategory::RegexInjection)
            .with_dangerous_params(vec![0])
            .with_severity(4),
    );
    registry.add(
        Sink::new("re.match", SinkCategory::RegexInjection)
            .with_dangerous_params(vec![0])
            .with_severity(4),
    );
    registry.add(
        Sink::new("re.search", SinkCategory::RegexInjection)
            .with_dangerous_params(vec![0])
            .with_severity(4),
    );
    registry.add(
        Sink::new("re.findall", SinkCategory::RegexInjection)
            .with_dangerous_params(vec![0])
            .with_severity(4),
    );
    registry.add(
        Sink::new("re.sub", SinkCategory::RegexInjection)
            .with_dangerous_params(vec![0])
            .with_severity(4),
    );
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_python_sql_sinks() {
        let registry = get_python_sinks();

        let matches = registry.find_matches("cursor.execute");
        assert!(!matches.is_empty());
        assert!(matches
            .iter()
            .any(|s| s.category == SinkCategory::SqlInjection));
    }

    #[test]
    fn test_python_command_sinks() {
        let registry = get_python_sinks();

        let matches = registry.find_matches("subprocess.run");
        assert!(!matches.is_empty());
        assert!(matches
            .iter()
            .any(|s| s.category == SinkCategory::CommandInjection));
    }

    #[test]
    fn test_python_pickle_sinks() {
        let registry = get_python_sinks();

        let matches = registry.find_matches("pickle.loads");
        assert!(!matches.is_empty());
        assert!(matches
            .iter()
            .any(|s| s.category == SinkCategory::Deserialization));
        assert!(matches.iter().any(|s| s.severity() == 10));
    }

    #[test]
    fn test_python_xss_sinks() {
        let registry = get_python_sinks();

        let matches = registry.find_matches("Markup(");
        assert!(!matches.is_empty());
        assert!(matches.iter().any(|s| s.category == SinkCategory::XSS));
    }

    #[test]
    fn test_python_ssrf_sinks() {
        let registry = get_python_sinks();

        let matches = registry.find_matches("requests.get");
        assert!(!matches.is_empty());
        assert!(matches.iter().any(|s| s.category == SinkCategory::SSRF));
    }

    #[test]
    fn test_python_path_sinks() {
        let registry = get_python_sinks();

        let matches = registry.find_matches("open(");
        assert!(!matches.is_empty());
        assert!(matches
            .iter()
            .any(|s| s.category == SinkCategory::PathTraversal));
    }

    #[test]
    fn test_sink_count() {
        let registry = get_python_sinks();
        // Should have comprehensive coverage
        assert!(registry.len() > 100);
    }

    #[test]
    fn test_sink_categories_covered() {
        let registry = get_python_sinks();
        let categories = registry.categories();

        // Should cover major categories
        assert!(categories.contains(&SinkCategory::SqlInjection));
        assert!(categories.contains(&SinkCategory::CommandInjection));
        assert!(categories.contains(&SinkCategory::XSS));
        assert!(categories.contains(&SinkCategory::PathTraversal));
        assert!(categories.contains(&SinkCategory::CodeExecution));
        assert!(categories.contains(&SinkCategory::SSRF));
        assert!(categories.contains(&SinkCategory::Deserialization));
    }
}
