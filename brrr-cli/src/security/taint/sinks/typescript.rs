//! TypeScript/JavaScript-specific taint sink definitions.
//!
//! This module contains comprehensive sink definitions for TypeScript and JavaScript
//! security analysis, covering major frameworks and libraries:
//!
//! - **SQL**: pg, mysql2, sqlite3, Prisma, TypeORM, Knex, Sequelize
//! - **Web (Server)**: Express, Fastify, Koa, Hapi, NestJS
//! - **Web (Client)**: DOM APIs, React, Vue, Angular
//! - **Command**: child_process
//! - **File**: fs, path
//! - **Network**: fetch, axios, http/https, got, node-fetch

use super::{Sink, SinkCategory, SinkRegistry};

/// Build the complete TypeScript/JavaScript sink registry.
pub fn get_typescript_sinks() -> SinkRegistry {
    let mut registry = SinkRegistry::new();

    // Add all sink categories
    add_sql_sinks(&mut registry);
    add_command_sinks(&mut registry);
    add_code_execution_sinks(&mut registry);
    add_path_sinks(&mut registry);
    add_xss_dom_sinks(&mut registry);
    add_xss_server_sinks(&mut registry);
    add_ssrf_sinks(&mut registry);
    add_deserialization_sinks(&mut registry);
    add_redirect_sinks(&mut registry);
    add_template_sinks(&mut registry);
    add_header_sinks(&mut registry);
    add_nosql_sinks(&mut registry);
    add_regex_sinks(&mut registry);
    add_prototype_pollution_sinks(&mut registry);

    registry
}

// =============================================================================
// SQL Injection Sinks
// =============================================================================

fn add_sql_sinks(registry: &mut SinkRegistry) {
    // Generic query methods
    registry.add(Sink::sql("query(", "Generic SQL query()"));
    registry.add(Sink::sql("execute(", "Generic SQL execute()"));

    // node-postgres (pg)
    registry.add(Sink::sql("client.query", "pg client.query()"));
    registry.add(Sink::sql("pool.query", "pg pool.query()"));
    registry.add(Sink::sql("Pool.query", "pg Pool.query()"));
    registry.add(Sink::sql("Client.query", "pg Client.query()"));

    // mysql2
    registry.add(Sink::sql("connection.query", "mysql2 connection.query()"));
    registry.add(Sink::sql(
        "connection.execute",
        "mysql2 connection.execute()",
    ));

    // sqlite3
    registry.add(Sink::sql("db.run", "sqlite3 db.run()"));
    registry.add(Sink::sql("db.get", "sqlite3 db.get()"));
    registry.add(Sink::sql("db.all", "sqlite3 db.all()"));
    registry.add(Sink::sql("db.each", "sqlite3 db.each()"));
    registry.add(Sink::sql("db.exec", "sqlite3 db.exec()"));
    registry.add(Sink::sql("db.prepare", "sqlite3 db.prepare()"));

    // better-sqlite3
    registry.add(Sink::sql("database.exec", "better-sqlite3 database.exec()"));
    registry.add(Sink::sql(
        "database.prepare",
        "better-sqlite3 database.prepare()",
    ));

    // Knex
    registry.add(Sink::sql(".raw(", "Knex raw() query").with_severity(9));
    registry.add(Sink::sql("knex.raw", "Knex knex.raw()"));
    registry.add(Sink::sql("knex.whereRaw", "Knex whereRaw()"));
    registry.add(Sink::sql("knex.havingRaw", "Knex havingRaw()"));
    registry.add(Sink::sql("knex.orderByRaw", "Knex orderByRaw()"));

    // Prisma
    registry.add(Sink::sql("$queryRaw", "Prisma $queryRaw()").with_severity(9));
    registry.add(Sink::sql("$executeRaw", "Prisma $executeRaw()").with_severity(9));
    registry.add(Sink::sql("$queryRawUnsafe", "Prisma $queryRawUnsafe()").with_severity(10));
    registry.add(Sink::sql("$executeRawUnsafe", "Prisma $executeRawUnsafe()").with_severity(10));

    // TypeORM
    registry.add(Sink::sql("manager.query", "TypeORM manager.query()"));
    registry.add(Sink::sql("repository.query", "TypeORM repository.query()"));
    registry.add(Sink::sql(
        "entityManager.query",
        "TypeORM entityManager.query()",
    ));
    registry.add(Sink::sql(
        "createQueryRunner",
        "TypeORM createQueryRunner()",
    ));
    registry.add(Sink::sql(
        "queryRunner.query",
        "TypeORM queryRunner.query()",
    ));

    // Sequelize
    registry.add(Sink::sql("sequelize.query", "Sequelize sequelize.query()"));
    registry.add(Sink::sql("Sequelize.query", "Sequelize Sequelize.query()"));
    registry.add(Sink::sql(
        "sequelize.literal",
        "Sequelize sequelize.literal()",
    ));

    // MikroORM
    registry.add(Sink::sql("em.execute", "MikroORM em.execute()"));
    registry.add(Sink::sql(
        "entityManager.execute",
        "MikroORM entityManager.execute()",
    ));

    // Drizzle ORM
    registry.add(Sink::sql("sql.raw", "Drizzle sql.raw()"));

    // mssql
    registry.add(Sink::sql("request.query", "mssql request.query()"));
    registry.add(Sink::sql("request.batch", "mssql request.batch()"));

    // oracledb
    registry.add(Sink::sql(
        "connection.execute",
        "oracledb connection.execute()",
    ));
}

// =============================================================================
// Command Injection Sinks
// =============================================================================

fn add_command_sinks(registry: &mut SinkRegistry) {
    // child_process module
    registry.add(
        Sink::command("child_process.exec", "child_process.exec() shell command").with_severity(10),
    );
    registry.add(
        Sink::command(
            "child_process.execSync",
            "child_process.execSync() sync shell command",
        )
        .with_severity(10),
    );
    registry.add(Sink::command(
        "child_process.spawn",
        "child_process.spawn()",
    ));
    registry.add(Sink::command(
        "child_process.spawnSync",
        "child_process.spawnSync()",
    ));
    registry.add(Sink::command(
        "child_process.execFile",
        "child_process.execFile()",
    ));
    registry.add(Sink::command(
        "child_process.execFileSync",
        "child_process.execFileSync()",
    ));
    registry.add(Sink::command("child_process.fork", "child_process.fork()"));

    // Shorthand imports
    registry.add(Sink::command("exec(", "exec() shell command").with_severity(10));
    registry.add(Sink::command("execSync(", "execSync() shell command").with_severity(10));
    registry.add(Sink::command("spawn(", "spawn() process"));
    registry.add(Sink::command("spawnSync(", "spawnSync() process"));
    registry.add(Sink::command("execFile(", "execFile() process"));
    registry.add(Sink::command("execFileSync(", "execFileSync() process"));

    // shelljs
    registry.add(Sink::command("shell.exec", "shelljs shell.exec()").with_severity(10));
    registry.add(Sink::command("shell.rm", "shelljs shell.rm()"));
    registry.add(Sink::command("shell.mv", "shelljs shell.mv()"));
    registry.add(Sink::command("shell.cp", "shelljs shell.cp()"));

    // execa
    registry.add(Sink::command("execa(", "execa() command execution"));
    registry.add(Sink::command("execaSync(", "execaSync() command execution"));
    registry.add(Sink::command("execaCommand(", "execaCommand() shell command").with_severity(10));
    registry.add(
        Sink::command("execaCommandSync(", "execaCommandSync() shell command").with_severity(10),
    );

    // cross-spawn
    registry.add(Sink::command("crossSpawn(", "cross-spawn execution"));
    registry.add(Sink::command(
        "crossSpawn.sync(",
        "cross-spawn sync execution",
    ));
}

// =============================================================================
// Code Execution Sinks
// =============================================================================

fn add_code_execution_sinks(registry: &mut SinkRegistry) {
    // eval and Function
    registry.add(Sink::code_exec("eval(", "eval() code execution").with_severity(10));
    registry.add(Sink::code_exec("Function(", "Function() constructor").with_severity(10));
    registry.add(Sink::code_exec("new Function(", "new Function() constructor").with_severity(10));

    // setTimeout/setInterval with strings
    registry.add(
        Sink::code_exec("setTimeout(", "setTimeout() with string code")
            .with_severity(7)
            .with_tag("string-first-arg"),
    );
    registry.add(
        Sink::code_exec("setInterval(", "setInterval() with string code")
            .with_severity(7)
            .with_tag("string-first-arg"),
    );

    // vm module (Node.js)
    registry.add(Sink::code_exec("vm.runInContext", "vm.runInContext()").with_severity(9));
    registry.add(Sink::code_exec("vm.runInNewContext", "vm.runInNewContext()").with_severity(9));
    registry.add(Sink::code_exec("vm.runInThisContext", "vm.runInThisContext()").with_severity(9));
    registry.add(Sink::code_exec(
        "vm.compileFunction",
        "vm.compileFunction()",
    ));
    registry.add(Sink::code_exec("vm.Script", "new vm.Script()"));
    registry.add(Sink::code_exec(
        "script.runInContext",
        "vm.Script.runInContext()",
    ));
    registry.add(Sink::code_exec(
        "script.runInNewContext",
        "vm.Script.runInNewContext()",
    ));

    // WebAssembly instantiation (lower risk)
    registry.add(
        Sink::code_exec("WebAssembly.instantiate", "WebAssembly.instantiate()").with_severity(6),
    );
    registry.add(Sink::code_exec("WebAssembly.compile", "WebAssembly.compile()").with_severity(6));
}

// =============================================================================
// Path Traversal Sinks
// =============================================================================

fn add_path_sinks(registry: &mut SinkRegistry) {
    // fs module (sync operations)
    registry.add(Sink::path("fs.readFile", "fs.readFile()"));
    registry.add(Sink::path("fs.readFileSync", "fs.readFileSync()"));
    registry.add(Sink::path("fs.writeFile", "fs.writeFile()"));
    registry.add(Sink::path("fs.writeFileSync", "fs.writeFileSync()"));
    registry.add(Sink::path("fs.appendFile", "fs.appendFile()"));
    registry.add(Sink::path("fs.appendFileSync", "fs.appendFileSync()"));
    registry.add(Sink::path("fs.unlink", "fs.unlink() file deletion"));
    registry.add(Sink::path("fs.unlinkSync", "fs.unlinkSync() file deletion"));
    registry.add(Sink::path("fs.rmdir", "fs.rmdir() directory removal"));
    registry.add(Sink::path(
        "fs.rmdirSync",
        "fs.rmdirSync() directory removal",
    ));
    registry.add(Sink::path("fs.rm", "fs.rm() removal").with_severity(9));
    registry.add(Sink::path("fs.rmSync", "fs.rmSync() removal").with_severity(9));
    registry.add(Sink::path("fs.rename", "fs.rename()"));
    registry.add(Sink::path("fs.renameSync", "fs.renameSync()"));
    registry.add(Sink::path("fs.mkdir", "fs.mkdir()"));
    registry.add(Sink::path("fs.mkdirSync", "fs.mkdirSync()"));
    registry.add(Sink::path("fs.readdir", "fs.readdir()"));
    registry.add(Sink::path("fs.readdirSync", "fs.readdirSync()"));
    registry.add(Sink::path("fs.stat", "fs.stat()"));
    registry.add(Sink::path("fs.statSync", "fs.statSync()"));
    registry.add(Sink::path("fs.access", "fs.access()"));
    registry.add(Sink::path("fs.accessSync", "fs.accessSync()"));
    registry.add(Sink::path("fs.chmod", "fs.chmod()"));
    registry.add(Sink::path("fs.chmodSync", "fs.chmodSync()"));
    registry.add(Sink::path("fs.chown", "fs.chown()"));
    registry.add(Sink::path("fs.chownSync", "fs.chownSync()"));
    registry.add(Sink::path("fs.link", "fs.link()"));
    registry.add(Sink::path("fs.linkSync", "fs.linkSync()"));
    registry.add(Sink::path("fs.symlink", "fs.symlink()"));
    registry.add(Sink::path("fs.symlinkSync", "fs.symlinkSync()"));
    registry.add(Sink::path("fs.truncate", "fs.truncate()"));
    registry.add(Sink::path("fs.truncateSync", "fs.truncateSync()"));
    registry.add(Sink::path("fs.open", "fs.open()"));
    registry.add(Sink::path("fs.openSync", "fs.openSync()"));
    registry.add(Sink::path("fs.createReadStream", "fs.createReadStream()"));
    registry.add(Sink::path("fs.createWriteStream", "fs.createWriteStream()"));
    registry.add(Sink::path("fs.copyFile", "fs.copyFile()"));
    registry.add(Sink::path("fs.copyFileSync", "fs.copyFileSync()"));

    // fs/promises
    registry.add(Sink::path("fsPromises.readFile", "fsPromises.readFile()"));
    registry.add(Sink::path("fsPromises.writeFile", "fsPromises.writeFile()"));
    registry.add(Sink::path("fsPromises.unlink", "fsPromises.unlink()"));
    registry.add(Sink::path("fsPromises.rm", "fsPromises.rm()"));
    registry.add(Sink::path("fsPromises.rmdir", "fsPromises.rmdir()"));

    // path module (lower severity - path construction)
    registry.add(Sink::path("path.join", "path.join() path construction").with_severity(5));
    registry.add(Sink::path("path.resolve", "path.resolve() path construction").with_severity(5));
    registry.add(Sink::path("path.normalize", "path.normalize()").with_severity(4));

    // Express static file serving
    registry
        .add(Sink::path("express.static", "express.static() directory serving").with_severity(7));
    registry.add(Sink::path("res.sendFile", "res.sendFile()"));
    registry.add(Sink::path("res.download", "res.download()"));

    // Archive extraction (zip slip)
    registry.add(Sink::path("extract(", "Archive extraction").with_severity(9));
    registry.add(Sink::path("unzip(", "Unzip extraction").with_severity(9));
    registry.add(Sink::path("tar.extract", "Tar extraction").with_severity(9));
    registry.add(Sink::path("AdmZip", "AdmZip extraction").with_severity(9));
}

// =============================================================================
// XSS Sinks (DOM/Client-side)
// =============================================================================

fn add_xss_dom_sinks(registry: &mut SinkRegistry) {
    // Direct HTML injection
    registry.add(
        Sink::xss("innerHTML", "DOM innerHTML property")
            .as_property()
            .with_severity(8),
    );
    registry.add(
        Sink::xss("outerHTML", "DOM outerHTML property")
            .as_property()
            .with_severity(8),
    );
    registry.add(Sink::xss("insertAdjacentHTML", "insertAdjacentHTML()"));
    registry.add(Sink::xss("document.write", "document.write()").with_severity(9));
    registry.add(Sink::xss("document.writeln", "document.writeln()").with_severity(9));

    // jQuery XSS sinks
    registry.add(Sink::xss("$(", "jQuery selector with HTML").with_severity(7));
    registry.add(Sink::xss("$.html(", "jQuery .html()").with_severity(8));
    registry.add(Sink::xss(".html(", "jQuery .html()").with_severity(8));
    registry.add(Sink::xss("$.append(", "jQuery .append()").with_severity(7));
    registry.add(Sink::xss(".append(", "jQuery .append()").with_severity(7));
    registry.add(Sink::xss("$.prepend(", "jQuery .prepend()").with_severity(7));
    registry.add(Sink::xss(".prepend(", "jQuery .prepend()").with_severity(7));
    registry.add(Sink::xss("$.after(", "jQuery .after()").with_severity(7));
    registry.add(Sink::xss("$.before(", "jQuery .before()").with_severity(7));
    registry.add(Sink::xss("$.replaceWith(", "jQuery .replaceWith()").with_severity(7));
    registry.add(Sink::xss("$.wrap(", "jQuery .wrap()").with_severity(6));

    // React
    registry.add(
        Sink::xss("dangerouslySetInnerHTML", "React dangerouslySetInnerHTML")
            .as_property()
            .with_severity(8),
    );

    // Angular
    registry.add(
        Sink::xss(
            "bypassSecurityTrustHtml",
            "Angular bypassSecurityTrustHtml()",
        )
        .with_severity(9),
    );
    registry.add(
        Sink::xss(
            "bypassSecurityTrustScript",
            "Angular bypassSecurityTrustScript()",
        )
        .with_severity(10),
    );
    registry.add(
        Sink::xss(
            "bypassSecurityTrustStyle",
            "Angular bypassSecurityTrustStyle()",
        )
        .with_severity(6),
    );
    registry.add(
        Sink::xss("bypassSecurityTrustUrl", "Angular bypassSecurityTrustUrl()").with_severity(7),
    );
    registry.add(
        Sink::xss(
            "bypassSecurityTrustResourceUrl",
            "Angular bypassSecurityTrustResourceUrl()",
        )
        .with_severity(8),
    );

    // Vue
    registry.add(
        Sink::xss("v-html", "Vue v-html directive")
            .as_property()
            .with_severity(8),
    );

    // URL-based XSS
    registry.add(
        Sink::xss("location.href", "location.href assignment")
            .as_property()
            .with_severity(6),
    );
    registry.add(Sink::xss("location.replace", "location.replace()"));
    registry.add(Sink::xss("location.assign", "location.assign()"));
    registry.add(Sink::xss("window.open", "window.open()"));

    // Attribute-based XSS
    registry.add(Sink::xss(".setAttribute(", "setAttribute()").with_severity(6));
    registry.add(
        Sink::xss(".src", "src attribute")
            .as_property()
            .with_severity(6),
    );
    registry.add(
        Sink::xss(".href", "href attribute")
            .as_property()
            .with_severity(6),
    );
}

// =============================================================================
// XSS Sinks (Server-side)
// =============================================================================

fn add_xss_server_sinks(registry: &mut SinkRegistry) {
    // Express
    registry.add(Sink::xss("res.send", "Express res.send()").with_severity(5));
    registry.add(Sink::xss("res.write", "Response res.write()").with_severity(5));
    registry.add(Sink::xss("res.end", "Response res.end()").with_severity(5));
    registry.add(Sink::xss("res.render", "Express res.render()").with_severity(4));

    // Fastify
    registry.add(Sink::xss("reply.send", "Fastify reply.send()").with_severity(5));
    registry.add(Sink::xss("reply.html", "Fastify reply.html()").with_severity(6));

    // Koa
    registry.add(
        Sink::xss("ctx.body", "Koa ctx.body")
            .as_property()
            .with_severity(5),
    );

    // Hapi
    registry.add(Sink::xss("h.response", "Hapi h.response()").with_severity(5));
}

// =============================================================================
// SSRF Sinks
// =============================================================================

fn add_ssrf_sinks(registry: &mut SinkRegistry) {
    // Fetch API
    registry.add(Sink::ssrf("fetch(", "fetch() API"));
    registry.add(Sink::ssrf("globalThis.fetch", "globalThis.fetch()"));
    registry.add(Sink::ssrf("window.fetch", "window.fetch()"));

    // axios
    registry.add(Sink::ssrf("axios(", "axios() request"));
    registry.add(Sink::ssrf("axios.get", "axios.get()"));
    registry.add(Sink::ssrf("axios.post", "axios.post()"));
    registry.add(Sink::ssrf("axios.put", "axios.put()"));
    registry.add(Sink::ssrf("axios.delete", "axios.delete()"));
    registry.add(Sink::ssrf("axios.patch", "axios.patch()"));
    registry.add(Sink::ssrf("axios.request", "axios.request()"));
    registry.add(Sink::ssrf("axios.create", "axios.create() instance"));

    // node-fetch
    registry.add(Sink::ssrf("nodeFetch(", "node-fetch()"));

    // got
    registry.add(Sink::ssrf("got(", "got() HTTP client"));
    registry.add(Sink::ssrf("got.get", "got.get()"));
    registry.add(Sink::ssrf("got.post", "got.post()"));
    registry.add(Sink::ssrf("got.extend", "got.extend()"));

    // request (deprecated but still used)
    registry.add(Sink::ssrf("request(", "request() (deprecated)").with_tag("deprecated"));
    registry.add(Sink::ssrf("request.get", "request.get()"));
    registry.add(Sink::ssrf("request.post", "request.post()"));

    // superagent
    registry.add(Sink::ssrf("superagent.get", "superagent.get()"));
    registry.add(Sink::ssrf("superagent.post", "superagent.post()"));

    // http/https modules
    registry.add(Sink::ssrf("http.request", "http.request()"));
    registry.add(Sink::ssrf("http.get", "http.get()"));
    registry.add(Sink::ssrf("https.request", "https.request()"));
    registry.add(Sink::ssrf("https.get", "https.get()"));

    // XMLHttpRequest
    registry.add(Sink::ssrf("XMLHttpRequest", "new XMLHttpRequest()"));
    registry.add(Sink::ssrf("xhr.open", "XMLHttpRequest.open()"));

    // WebSocket
    registry.add(Sink::ssrf("WebSocket(", "new WebSocket()").with_severity(6));
    registry.add(Sink::ssrf("new WebSocket", "new WebSocket()"));
}

// =============================================================================
// Deserialization Sinks
// =============================================================================

fn add_deserialization_sinks(registry: &mut SinkRegistry) {
    // JSON.parse (generally safe but can be exploited in some contexts)
    registry.add(Sink::new("JSON.parse", SinkCategory::Deserialization).with_severity(4));

    // node-serialize (RCE vulnerability)
    registry
        .add(Sink::new("serialize.unserialize", SinkCategory::Deserialization).with_severity(10));
    registry.add(Sink::new("node-serialize", SinkCategory::Deserialization).with_severity(10));

    // js-yaml
    registry.add(Sink::new("yaml.load", SinkCategory::Deserialization).with_severity(7));
    registry.add(Sink::new("yaml.loadAll", SinkCategory::Deserialization).with_severity(7));

    // xml2js (XXE possible)
    registry.add(Sink::new("xml2js.parseString", SinkCategory::Deserialization).with_severity(6));

    // fast-xml-parser
    registry.add(Sink::new("XMLParser.parse", SinkCategory::Deserialization).with_severity(5));

    // msgpack
    registry.add(Sink::new("msgpack.decode", SinkCategory::Deserialization).with_severity(5));

    // flatbuffers/protobuf (generally safe)
    registry.add(Sink::new("protobuf.decode", SinkCategory::Deserialization).with_severity(3));
}

// =============================================================================
// Open Redirect Sinks
// =============================================================================

fn add_redirect_sinks(registry: &mut SinkRegistry) {
    // Express
    registry
        .add(Sink::new("res.redirect", SinkCategory::OpenRedirect).with_dangerous_params(vec![0]));

    // Fastify
    registry.add(
        Sink::new("reply.redirect", SinkCategory::OpenRedirect).with_dangerous_params(vec![0]),
    );

    // Koa
    registry
        .add(Sink::new("ctx.redirect", SinkCategory::OpenRedirect).with_dangerous_params(vec![0]));

    // Browser APIs
    registry.add(Sink::new("location.href", SinkCategory::OpenRedirect).as_property());
    registry.add(
        Sink::new("location.replace", SinkCategory::OpenRedirect).with_dangerous_params(vec![0]),
    );
    registry.add(
        Sink::new("location.assign", SinkCategory::OpenRedirect).with_dangerous_params(vec![0]),
    );
    registry.add(Sink::new("window.location", SinkCategory::OpenRedirect).as_property());
    registry.add(Sink::new("document.location", SinkCategory::OpenRedirect).as_property());
}

// =============================================================================
// Template Injection Sinks
// =============================================================================

fn add_template_sinks(registry: &mut SinkRegistry) {
    // EJS
    registry.add(Sink::new("ejs.render", SinkCategory::TemplateInjection).with_severity(8));
    registry.add(Sink::new("ejs.compile", SinkCategory::TemplateInjection).with_severity(8));
    registry.add(Sink::new("ejs.renderFile", SinkCategory::TemplateInjection).with_severity(7));

    // Pug (Jade)
    registry.add(Sink::new("pug.render", SinkCategory::TemplateInjection).with_severity(8));
    registry.add(Sink::new("pug.compile", SinkCategory::TemplateInjection).with_severity(8));

    // Handlebars
    registry.add(Sink::new("Handlebars.compile", SinkCategory::TemplateInjection).with_severity(7));
    registry.add(Sink::new("handlebars.compile", SinkCategory::TemplateInjection).with_severity(7));

    // Mustache
    registry.add(Sink::new("Mustache.render", SinkCategory::TemplateInjection).with_severity(6));

    // Lodash template
    registry.add(Sink::new("_.template", SinkCategory::TemplateInjection).with_severity(9));
    registry.add(Sink::new("lodash.template", SinkCategory::TemplateInjection).with_severity(9));

    // Nunjucks
    registry
        .add(Sink::new("nunjucks.renderString", SinkCategory::TemplateInjection).with_severity(8));
    registry.add(Sink::new("nunjucks.compile", SinkCategory::TemplateInjection).with_severity(8));

    // doT.js
    registry.add(Sink::new("doT.template", SinkCategory::TemplateInjection).with_severity(9));

    // Marko
    registry.add(Sink::new("marko.load", SinkCategory::TemplateInjection).with_severity(7));
}

// =============================================================================
// HTTP Header Injection Sinks
// =============================================================================

fn add_header_sinks(registry: &mut SinkRegistry) {
    // Express/Node.js
    registry.add(Sink::header("res.setHeader", "res.setHeader()"));
    registry.add(Sink::header("res.set", "Express res.set()"));
    registry.add(Sink::header("res.header", "Express res.header()"));
    registry.add(Sink::header("response.setHeader", "response.setHeader()"));

    // Fastify
    registry.add(Sink::header("reply.header", "Fastify reply.header()"));

    // Koa
    registry.add(Sink::header("ctx.set", "Koa ctx.set()"));
}

// =============================================================================
// NoSQL Injection Sinks
// =============================================================================

fn add_nosql_sinks(registry: &mut SinkRegistry) {
    // MongoDB native driver
    registry.add(
        Sink::new("collection.find", SinkCategory::NoSqlInjection).with_dangerous_params(vec![0]),
    );
    registry.add(
        Sink::new("collection.findOne", SinkCategory::NoSqlInjection)
            .with_dangerous_params(vec![0]),
    );
    registry.add(
        Sink::new("collection.findOneAndUpdate", SinkCategory::NoSqlInjection)
            .with_dangerous_params(vec![0, 1]),
    );
    registry.add(
        Sink::new("collection.findOneAndDelete", SinkCategory::NoSqlInjection)
            .with_dangerous_params(vec![0]),
    );
    registry.add(
        Sink::new("collection.findOneAndReplace", SinkCategory::NoSqlInjection)
            .with_dangerous_params(vec![0, 1]),
    );
    registry.add(
        Sink::new("collection.updateOne", SinkCategory::NoSqlInjection)
            .with_dangerous_params(vec![0, 1]),
    );
    registry.add(
        Sink::new("collection.updateMany", SinkCategory::NoSqlInjection)
            .with_dangerous_params(vec![0, 1]),
    );
    registry.add(
        Sink::new("collection.deleteOne", SinkCategory::NoSqlInjection)
            .with_dangerous_params(vec![0]),
    );
    registry.add(
        Sink::new("collection.deleteMany", SinkCategory::NoSqlInjection)
            .with_dangerous_params(vec![0]),
    );
    registry.add(
        Sink::new("collection.aggregate", SinkCategory::NoSqlInjection)
            .with_dangerous_params(vec![0]),
    );
    registry.add(
        Sink::new("collection.distinct", SinkCategory::NoSqlInjection)
            .with_dangerous_params(vec![1]),
    );

    // Mongoose
    registry
        .add(Sink::new("Model.find", SinkCategory::NoSqlInjection).with_dangerous_params(vec![0]));
    registry.add(
        Sink::new("Model.findOne", SinkCategory::NoSqlInjection).with_dangerous_params(vec![0]),
    );
    registry.add(
        Sink::new("Model.findById", SinkCategory::NoSqlInjection).with_dangerous_params(vec![0]),
    );
    registry.add(Sink::new("Model.where", SinkCategory::NoSqlInjection));
    registry.add(Sink::new("Model.$where", SinkCategory::NoSqlInjection).with_severity(10));

    // Redis
    registry.add(Sink::new("redis.eval", SinkCategory::NoSqlInjection).with_severity(9));
    registry.add(Sink::new("client.eval", SinkCategory::NoSqlInjection).with_severity(9));
}

// =============================================================================
// Regular Expression Injection Sinks
// =============================================================================

fn add_regex_sinks(registry: &mut SinkRegistry) {
    // RegExp constructor
    registry.add(
        Sink::new("RegExp(", SinkCategory::RegexInjection)
            .with_dangerous_params(vec![0])
            .with_severity(4),
    );
    registry.add(
        Sink::new("new RegExp", SinkCategory::RegexInjection)
            .with_dangerous_params(vec![0])
            .with_severity(4),
    );

    // String methods with regex
    registry.add(Sink::new(".match(", SinkCategory::RegexInjection).with_severity(3));
    registry.add(Sink::new(".replace(", SinkCategory::RegexInjection).with_severity(3));
    registry.add(Sink::new(".search(", SinkCategory::RegexInjection).with_severity(3));
    registry.add(Sink::new(".split(", SinkCategory::RegexInjection).with_severity(3));
}

// =============================================================================
// Prototype Pollution Sinks (JavaScript-specific)
// =============================================================================

fn add_prototype_pollution_sinks(registry: &mut SinkRegistry) {
    // Object merge/extend operations
    registry.add(
        Sink::new("Object.assign", SinkCategory::CodeExecution)
            .with_severity(5)
            .with_tag("prototype-pollution"),
    );
    registry.add(
        Sink::new("_.merge", SinkCategory::CodeExecution)
            .with_severity(7)
            .with_tag("prototype-pollution"),
    );
    registry.add(
        Sink::new("_.extend", SinkCategory::CodeExecution)
            .with_severity(7)
            .with_tag("prototype-pollution"),
    );
    registry.add(
        Sink::new("_.defaultsDeep", SinkCategory::CodeExecution)
            .with_severity(8)
            .with_tag("prototype-pollution"),
    );
    registry.add(
        Sink::new("$.extend", SinkCategory::CodeExecution)
            .with_severity(7)
            .with_tag("prototype-pollution"),
    );
    registry.add(
        Sink::new("deepmerge", SinkCategory::CodeExecution)
            .with_severity(7)
            .with_tag("prototype-pollution"),
    );
    registry.add(
        Sink::new("merge-deep", SinkCategory::CodeExecution)
            .with_severity(7)
            .with_tag("prototype-pollution"),
    );
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_typescript_sql_sinks() {
        let registry = get_typescript_sinks();

        let matches = registry.find_matches("pool.query");
        assert!(!matches.is_empty());
        assert!(matches
            .iter()
            .any(|s| s.category == SinkCategory::SqlInjection));
    }

    #[test]
    fn test_typescript_command_sinks() {
        let registry = get_typescript_sinks();

        let matches = registry.find_matches("child_process.exec");
        assert!(!matches.is_empty());
        assert!(matches
            .iter()
            .any(|s| s.category == SinkCategory::CommandInjection));
    }

    #[test]
    fn test_typescript_xss_sinks() {
        let registry = get_typescript_sinks();

        let matches = registry.find_matches("innerHTML");
        assert!(!matches.is_empty());
        assert!(matches.iter().any(|s| s.category == SinkCategory::XSS));
    }

    #[test]
    fn test_typescript_ssrf_sinks() {
        let registry = get_typescript_sinks();

        let matches = registry.find_matches("fetch(");
        assert!(!matches.is_empty());
        assert!(matches.iter().any(|s| s.category == SinkCategory::SSRF));
    }

    #[test]
    fn test_typescript_path_sinks() {
        let registry = get_typescript_sinks();

        let matches = registry.find_matches("fs.readFile");
        assert!(!matches.is_empty());
        assert!(matches
            .iter()
            .any(|s| s.category == SinkCategory::PathTraversal));
    }

    #[test]
    fn test_prisma_raw_sinks() {
        let registry = get_typescript_sinks();

        let matches = registry.find_matches("$queryRawUnsafe");
        assert!(!matches.is_empty());
        assert!(matches.iter().any(|s| s.severity() == 10));
    }

    #[test]
    fn test_react_dangerously_set() {
        let registry = get_typescript_sinks();

        let matches = registry.find_matches("dangerouslySetInnerHTML");
        assert!(!matches.is_empty());
        assert!(matches.iter().any(|s| s.category == SinkCategory::XSS));
        assert!(matches.iter().any(|s| s.is_property));
    }

    #[test]
    fn test_sink_count() {
        let registry = get_typescript_sinks();
        // Should have comprehensive coverage
        assert!(registry.len() > 100);
    }

    #[test]
    fn test_sink_categories_covered() {
        let registry = get_typescript_sinks();
        let categories = registry.categories();

        // Should cover major categories
        assert!(categories.contains(&SinkCategory::SqlInjection));
        assert!(categories.contains(&SinkCategory::CommandInjection));
        assert!(categories.contains(&SinkCategory::XSS));
        assert!(categories.contains(&SinkCategory::PathTraversal));
        assert!(categories.contains(&SinkCategory::CodeExecution));
        assert!(categories.contains(&SinkCategory::SSRF));
    }
}
