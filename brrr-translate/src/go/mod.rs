//! Go language translation to Brrr IR.
//!
//! This module translates Go source code (parsed via tree-sitter-go)
//! into the brrr-repr intermediate representation.
//!
//! # Go to Brrr Mapping
//!
//! ## Types
//! - `bool` → `Prim(Bool)`
//! - `int8..int64` → `Numeric(I8..I64)`
//! - `uint8..uint64` → `Numeric(U8..U64)`
//! - `float32/64` → `Numeric(F32/F64)`
//! - `string` → `Prim(String)`
//! - `[]T` → `Wrap(Slice, T)`
//! - `[N]T` → `Wrap(Array, T)`
//! - `*T` → `Wrap(Option, T)` (nullable pointer)
//! - `chan T` → `App(Named("Chan"), [T])` + SessionType
//! - `struct{...}` → `Struct(StructType)`
//! - `interface{...}` → `Named(name)` (existential)
//! - `func(P)(R)` → `Func(FuncType)` with Go effects
//!
//! ## Concurrency
//! - `go f(x)` → `Spawn(Call(f, [x]))` + ESpawn effect
//! - `ch <- v` → `Perform(ESend, [v])` (session effect)
//! - `<-ch` → `Perform(ERecv, [])` (session effect)
//! - `select {...}` → `Match` with session branching

mod context;
mod types;
mod exprs;
mod stmts;
mod concurrency;

pub use context::GoTranslationContext;

use crate::{TranslateError, TranslateErrorKind, TranslateResult, TranslatedModule, TranslationContext};
use brrr_repr::decl::{Declaration, Module};
use brrr_repr::BrrrType;
use tree_sitter::Node;

/// Go to Brrr IR translator.
///
/// Translates Go source files into brrr-repr IR modules.
pub struct GoTranslator<'src> {
    ctx: GoTranslationContext<'src>,
}

impl<'src> GoTranslator<'src> {
    /// Create a new Go translator for the given source.
    pub fn new(source: &'src [u8]) -> Self {
        Self {
            ctx: GoTranslationContext::new(source),
        }
    }

    /// Parse Go source code into a tree.
    fn parse(&self) -> TranslateResult<tree_sitter::Tree> {
        let mut parser = tree_sitter::Parser::new();
        parser
            .set_language(&tree_sitter_go::LANGUAGE.into())
            .map_err(|e| TranslateError {
                kind: TranslateErrorKind::ParseError,
                message: format!("Failed to set Go language: {}", e),
                line: 0,
                column: 0,
            })?;

        parser
            .parse(self.ctx.source_bytes(), None)
            .ok_or_else(|| TranslateError {
                kind: TranslateErrorKind::ParseError,
                message: "Failed to parse Go source".to_string(),
                line: 0,
                column: 0,
            })
    }

    /// Parse and translate Go source to a Brrr module (metadata only).
    pub fn translate_source(&mut self) -> TranslateResult<Module> {
        let tree = self.parse()?;
        translate_source_file_impl(&mut self.ctx, tree.root_node())
    }

    /// Parse and translate Go source to a full TranslatedModule with function bodies.
    pub fn translate(&mut self) -> TranslateResult<TranslatedModule> {
        let tree = self.parse()?;
        translate_full_impl(&mut self.ctx, tree.root_node())
    }

}

/// Translate a source_file node to a Module (metadata only).
fn translate_source_file_impl<'src>(
    ctx: &mut GoTranslationContext<'src>,
    root: Node<'_>,
) -> TranslateResult<Module> {
    debug_assert_eq!(root.kind(), "source_file");

    let mut declarations = Vec::new();

    // Iterate over top-level declarations
    let mut cursor = root.walk();
    for child in root.children(&mut cursor) {
        match child.kind() {
            "package_clause" => {
                // Extract package name for module
                if let Some(name_node) = child.child_by_field_name("name") {
                    let pkg_name = ctx.node_text(name_node);
                    ctx.set_package_name(pkg_name);
                }
            }
            "import_declaration" => {
                if let Ok(imports) = translate_imports(ctx, child) {
                    for imp in imports {
                        ctx.add_import(imp);
                    }
                }
            }
            "function_declaration" => {
                if let Ok(decl) = types::translate_function_decl(ctx, child) {
                    declarations.push(decl);
                }
            }
            "method_declaration" => {
                if let Ok(decl) = types::translate_method_decl(ctx, child) {
                    declarations.push(decl);
                }
            }
            "type_declaration" => {
                if let Ok(decls) = types::translate_type_decl(ctx, child) {
                    declarations.extend(decls);
                }
            }
            "var_declaration" => {
                if let Ok(vars) = translate_package_vars(ctx, child) {
                    for var in vars {
                        // Add to declarations
                        declarations.push(Declaration::Variable {
                            name: var.name.clone(),
                            is_public: var.is_public,
                            span: var.span.clone(),
                        });
                    }
                }
            }
            "const_declaration" => {
                if let Ok(consts) = translate_package_consts(ctx, child) {
                    for constant in consts {
                        declarations.push(Declaration::Constant {
                            name: constant.name.clone(),
                            is_public: constant.is_public,
                            span: constant.span.clone(),
                        });
                    }
                }
            }
            "comment" | "\n" => {
                // Skip comments and whitespace
            }
            _ => {
                // Unknown top-level construct
            }
        }
    }

    Ok(Module {
        name: ctx.package_name().to_string(),
        path: vec![ctx.package_name().to_string()],
        imports: Vec::new(),
        declarations,
        submodules: Vec::new(),
        span: brrr_repr::expr::Range::SYNTHETIC,
    })
}

/// Translate a source_file node to a full TranslatedModule with bodies.
fn translate_full_impl<'src>(
    ctx: &mut GoTranslationContext<'src>,
    root: Node<'_>,
) -> TranslateResult<TranslatedModule> {
    debug_assert_eq!(root.kind(), "source_file");

    // First pass: extract package name
    let mut cursor = root.walk();
    for child in root.children(&mut cursor) {
        if child.kind() == "package_clause" {
            if let Some(name_node) = child.child_by_field_name("name") {
                let pkg_name = ctx.node_text(name_node);
                ctx.set_package_name(pkg_name);
            }
        }
    }

    // Create base module
    let base_module = Module {
        name: ctx.package_name().to_string(),
        path: vec![ctx.package_name().to_string()],
        imports: Vec::new(),
        declarations: Vec::new(),
        submodules: Vec::new(),
        span: brrr_repr::expr::Range::SYNTHETIC,
    };

    let mut result = TranslatedModule::new(base_module);

    // Second pass: translate all declarations
    let mut cursor = root.walk();
    for child in root.children(&mut cursor) {
        match child.kind() {
            "function_declaration" => {
                if let Ok(func_def) = types::translate_function_def(ctx, child) {
                    result.add_function(func_def);
                }
            }
            "method_declaration" => {
                if let Ok(func_def) = types::translate_method_def(ctx, child) {
                    result.add_function(func_def);
                }
            }
            "type_declaration" => {
                // TODO: Add full type definitions
                if let Ok(decls) = types::translate_type_decl(ctx, child) {
                    for decl in decls {
                        result.module.declarations.push(decl);
                    }
                }
            }
            "var_declaration" => {
                if let Ok(vars) = translate_package_vars(ctx, child) {
                    for var in vars {
                        result.add_variable(var);
                    }
                }
            }
            "const_declaration" => {
                if let Ok(consts) = translate_package_consts(ctx, child) {
                    for constant in consts {
                        result.add_constant(constant);
                    }
                }
            }
            "import_declaration" => {
                if let Ok(imports) = translate_imports(ctx, child) {
                    for imp in imports {
                        result.module.imports.push(imp);
                    }
                }
            }
            _ => {}
        }
    }

    Ok(result)
}

/// Translate an import declaration to a list of imports.
fn translate_imports<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Vec<brrr_repr::decl::Import>> {
    let mut imports = Vec::new();

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        match child.kind() {
            "import_spec" => {
                if let Ok(import) = translate_import_spec(ctx, child) {
                    imports.push(import);
                }
            }
            "import_spec_list" => {
                // Handle grouped imports: import ( "pkg1"; "pkg2" )
                let mut spec_cursor = child.walk();
                for spec in child.children(&mut spec_cursor) {
                    if spec.kind() == "import_spec" {
                        if let Ok(import) = translate_import_spec(ctx, spec) {
                            imports.push(import);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    Ok(imports)
}

/// Translate a single import spec.
fn translate_import_spec<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<brrr_repr::decl::Import> {
    use brrr_repr::decl::{Import, ImportItem, ImportItems};

    // import_spec: [alias] path
    let path_node = node.child_by_field_name("path")
        .ok_or_else(|| crate::missing_node("import path", node))?;

    // Path is a string literal, remove quotes
    let path_text = ctx.node_text(path_node);
    let path = path_text.trim_matches('"').to_string();

    // Extract package name from path (last component)
    let pkg_name = path.rsplit('/').next().unwrap_or(&path).to_string();

    // Check for alias
    let alias_node = node.child_by_field_name("name");
    let alias_text = alias_node.map(|n| ctx.node_text(n).to_string());

    // Convert Go import to Brrr Import structure
    let module_path: Vec<String> = path.split('/').map(String::from).collect();

    // Determine import items based on alias
    let (items, module_alias) = match alias_text.as_deref() {
        Some(".") => {
            // Dot import: `import . "pkg"` - import all items
            (ImportItems::All, None)
        }
        Some("_") => {
            // Blank import: `import _ "pkg"` - side effect only
            // Represented as empty named import with no alias
            (ImportItems::Named(Vec::new()), None)
        }
        Some(alias) => {
            // Aliased import: `import alias "pkg"`
            (ImportItems::Named(vec![ImportItem::simple(pkg_name)]), Some(alias.to_string()))
        }
        None => {
            // Normal import: `import "pkg"`
            (ImportItems::Named(vec![ImportItem::simple(pkg_name)]), None)
        }
    };

    Ok(Import {
        module_path,
        alias: module_alias,
        items,
        span: exprs::node_range(node),
    })
}

/// Translate package-level variable declarations.
fn translate_package_vars<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Vec<crate::VariableDef>> {
    let mut vars = Vec::new();

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "var_spec" {
            if let Ok(var_defs) = translate_var_spec_to_def(ctx, child) {
                vars.extend(var_defs);
            }
        }
    }

    Ok(vars)
}

/// Translate a single var spec to VariableDef.
fn translate_var_spec_to_def<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Vec<crate::VariableDef>> {
    let mut vars = Vec::new();
    let range = exprs::node_range(node);

    // Collect names
    let mut names = Vec::new();
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "identifier" {
            names.push(ctx.node_text(child).to_string());
        }
    }

    // Get optional type
    let ty = node.child_by_field_name("type")
        .map(|t| types::translate_type(ctx, t))
        .transpose()?
        .unwrap_or(BrrrType::UNKNOWN);

    // Get optional initializer(s)
    let mut initializers = Vec::new();
    if let Some(value_node) = node.child_by_field_name("value") {
        let mut val_cursor = value_node.walk();
        for val_child in value_node.children(&mut val_cursor) {
            if val_child.kind() != "," {
                if let Ok(init_expr) = exprs::translate_expr(ctx, val_child) {
                    initializers.push(init_expr);
                }
            }
        }
    }

    // Create VariableDef for each name
    for (i, name) in names.into_iter().enumerate() {
        let is_public = name.chars().next().map(|c| c.is_uppercase()).unwrap_or(false);
        let initializer = initializers.get(i).cloned();

        vars.push(crate::VariableDef {
            name,
            ty: ty.clone(),
            initializer,
            is_public,
            span: range.clone(),
        });
    }

    Ok(vars)
}

/// Translate package-level const declarations.
fn translate_package_consts<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Vec<crate::ConstantDef>> {
    let mut consts = Vec::new();

    // Start iota counter for this const block
    ctx.start_const_block();

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "const_spec" {
            if let Ok(const_defs) = translate_const_spec_to_def(ctx, child) {
                consts.extend(const_defs);
            }
            // Increment iota after each spec
            ctx.next_iota();
        }
    }

    ctx.end_const_block();

    Ok(consts)
}

/// Translate a single const spec to ConstantDef.
fn translate_const_spec_to_def<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Vec<crate::ConstantDef>> {
    use brrr_repr::expr::{Expr_, Literal, WithLoc};
    use brrr_repr::types::IntType;

    let mut consts = Vec::new();
    let range = exprs::node_range(node);

    // Collect names
    let mut names = Vec::new();
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "identifier" {
            names.push(ctx.node_text(child).to_string());
        }
    }

    // Get optional type
    let ty = node.child_by_field_name("type")
        .map(|t| types::translate_type(ctx, t))
        .transpose()?
        .unwrap_or(BrrrType::UNKNOWN);

    // Get value expression(s)
    let mut values = Vec::new();
    if let Some(value_node) = node.child_by_field_name("value") {
        // Check if it's an expression_list or single expression
        if value_node.kind() == "expression_list" {
            let mut val_cursor = value_node.walk();
            for val_child in value_node.children(&mut val_cursor) {
                if val_child.kind() != "," {
                    // Check for iota
                    if ctx.node_text(val_child) == "iota" {
                        if let Some(iota_val) = ctx.current_iota() {
                            values.push(WithLoc::new(
                                Expr_::Lit(Literal::Int(iota_val, IntType::I64)),
                                range.clone(),
                            ));
                        }
                    } else if let Ok(val_expr) = exprs::translate_expr(ctx, val_child) {
                        values.push(val_expr);
                    }
                }
            }
        } else {
            // Single expression
            if ctx.node_text(value_node) == "iota" {
                if let Some(iota_val) = ctx.current_iota() {
                    values.push(WithLoc::new(
                        Expr_::Lit(Literal::Int(iota_val, IntType::I64)),
                        range.clone(),
                    ));
                }
            } else if let Ok(val_expr) = exprs::translate_expr(ctx, value_node) {
                values.push(val_expr);
            }
        }
    }

    // Create ConstantDef for each name
    for (i, name) in names.into_iter().enumerate() {
        let is_public = name.chars().next().map(|c| c.is_uppercase()).unwrap_or(false);
        let value = values.get(i).cloned().unwrap_or_else(|| {
            // Use default value (unit/zero)
            WithLoc::new(Expr_::Lit(Literal::Unit), range.clone())
        });

        consts.push(crate::ConstantDef {
            name,
            ty: ty.clone(),
            value,
            is_public,
            span: range.clone(),
        });
    }

    Ok(consts)
}

/// Translate a Go expression node to Brrr Expr.
pub fn translate_expr<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<brrr_repr::Expr> {
    exprs::translate_expr(ctx, node)
}

/// Translate a Go statement node to Brrr Expr.
pub fn translate_stmt<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<brrr_repr::Expr> {
    stmts::translate_stmt(ctx, node)
}

/// Translate a Go type node to BrrrType.
pub fn translate_type<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<BrrrType> {
    types::translate_type(ctx, node)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_package() {
        let source = b"package main\n";
        let mut translator = GoTranslator::new(source);
        let module = translator.translate_source().unwrap();
        assert_eq!(module.declarations.len(), 0);
    }

    #[test]
    fn test_simple_function() {
        let source = b"package main\n\nfunc add(x, y int) int {\n\treturn x + y\n}\n";
        let mut translator = GoTranslator::new(source);
        let module = translator.translate_source().unwrap();
        assert_eq!(module.declarations.len(), 1);
    }

    #[test]
    fn test_translate_full_function() {
        let source = b"package main\n\nfunc add(x, y int) int {\n\treturn x + y\n}\n";
        let mut translator = GoTranslator::new(source);
        let translated = translator.translate().unwrap();

        // Should have one function with body
        assert_eq!(translated.functions.len(), 1);

        // Function should have a body
        let func = &translated.functions[0];
        assert!(func.body.is_some(), "Function should have a body");

        // Function should have parameters
        assert_eq!(func.params.len(), 2, "Function should have 2 parameters");
    }

    #[test]
    fn test_translate_method() {
        let source = b"package main\n\ntype Counter struct { count int }\n\nfunc (c *Counter) Inc() {\n\tc.count++\n}\n";
        let mut translator = GoTranslator::new(source);
        let translated = translator.translate().unwrap();

        // Should have one method with receiver
        assert_eq!(translated.functions.len(), 1);

        // Method should have receiver as first parameter
        let method = &translated.functions[0];
        assert!(method.params.len() >= 1, "Method should have at least receiver parameter");
    }

    #[test]
    fn test_translate_multiple_functions() {
        let source = b"package main\n\nfunc foo() {}\n\nfunc bar() int { return 42 }\n\nfunc baz(x int) int { return x * 2 }\n";
        let mut translator = GoTranslator::new(source);
        let translated = translator.translate().unwrap();

        assert_eq!(translated.functions.len(), 3);
    }

    #[test]
    fn test_import_single() {
        let source = b"package main\n\nimport \"fmt\"\n";
        let mut translator = GoTranslator::new(source);
        let translated = translator.translate().unwrap();

        assert_eq!(translated.module.imports.len(), 1);
        assert_eq!(translated.module.imports[0].module_path, vec!["fmt"]);
    }

    #[test]
    fn test_import_grouped() {
        let source = b"package main\n\nimport (\n\t\"fmt\"\n\t\"os\"\n)\n";
        let mut translator = GoTranslator::new(source);
        let translated = translator.translate().unwrap();

        assert_eq!(translated.module.imports.len(), 2);
    }

    #[test]
    fn test_import_aliased() {
        let source = b"package main\n\nimport f \"fmt\"\n";
        let mut translator = GoTranslator::new(source);
        let translated = translator.translate().unwrap();

        assert_eq!(translated.module.imports.len(), 1);
        assert!(translated.module.imports[0].alias.is_some());
        assert_eq!(translated.module.imports[0].alias.as_ref().unwrap(), "f");
    }

    #[test]
    fn test_import_dot() {
        let source = b"package main\n\nimport . \"fmt\"\n";
        let mut translator = GoTranslator::new(source);
        let translated = translator.translate().unwrap();

        assert_eq!(translated.module.imports.len(), 1);
        // Dot import should have ImportItems::All
        assert!(translated.module.imports[0].items.is_glob());
    }

    #[test]
    fn test_package_var() {
        let source = b"package main\n\nvar count int\n";
        let mut translator = GoTranslator::new(source);
        let translated = translator.translate().unwrap();

        assert_eq!(translated.variables.len(), 1);
        assert_eq!(translated.variables[0].name, "count");
    }

    #[test]
    fn test_package_var_with_init() {
        let source = b"package main\n\nvar message = \"hello\"\n";
        let mut translator = GoTranslator::new(source);
        let translated = translator.translate().unwrap();

        assert_eq!(translated.variables.len(), 1);
        assert!(translated.variables[0].initializer.is_some());
    }

    #[test]
    fn test_package_var_multiple() {
        let source = b"package main\n\nvar x, y int\n";
        let mut translator = GoTranslator::new(source);
        let translated = translator.translate().unwrap();

        assert_eq!(translated.variables.len(), 2);
    }

    #[test]
    fn test_package_const() {
        let source = b"package main\n\nconst MaxSize = 100\n";
        let mut translator = GoTranslator::new(source);
        let translated = translator.translate().unwrap();

        assert_eq!(translated.constants.len(), 1);
        assert_eq!(translated.constants[0].name, "MaxSize");
        // Public because starts with uppercase
        assert!(translated.constants[0].is_public);
    }

    #[test]
    fn test_package_const_iota() {
        let source = b"package main\n\nconst (\n\tA = iota\n\tB\n\tC\n)\n";
        let mut translator = GoTranslator::new(source);
        let translated = translator.translate().unwrap();

        // Should have 3 constants
        assert_eq!(translated.constants.len(), 3);
    }

    #[test]
    fn test_exported_vs_unexported() {
        let source = b"package main\n\nvar PublicVar int\nvar privateVar int\nconst PublicConst = 1\nconst privateConst = 2\n";
        let mut translator = GoTranslator::new(source);
        let translated = translator.translate().unwrap();

        // Check exports
        assert_eq!(translated.variables.len(), 2);
        assert!(translated.variables[0].is_public); // PublicVar
        assert!(!translated.variables[1].is_public); // privateVar

        assert_eq!(translated.constants.len(), 2);
        assert!(translated.constants[0].is_public); // PublicConst
        assert!(!translated.constants[1].is_public); // privateConst
    }

    #[test]
    fn test_defer_lifo_semantics() {
        // Test that multiple defers are wrapped in correct LIFO order
        // Go: defer A(); defer B(); defer C(); return 42
        // Should produce Try-finally nesting where C runs first, B second, A last
        use brrr_repr::expr::Expr_;

        let source = b"package main\n\nfunc foo() int {\n\tdefer println(1)\n\tdefer println(2)\n\tdefer println(3)\n\treturn 42\n}\n";
        let mut translator = GoTranslator::new(source);
        let translated = translator.translate().unwrap();

        assert_eq!(translated.functions.len(), 1, "Should have 1 function");
        let func = &translated.functions[0];
        assert!(func.body.is_some(), "Function should have a body");

        // Verify the body is wrapped in nested Try-finally blocks
        let body = func.body.as_ref().unwrap();

        // Count the total number of Try expressions with finally blocks in the tree
        fn count_try_finally(expr: &brrr_repr::Expr) -> usize {
            match &expr.value {
                Expr_::Try { body, finally, catches } => {
                    let this = if finally.is_some() { 1 } else { 0 };
                    let body_count = count_try_finally(body);
                    let finally_count = finally.as_ref().map(|f| count_try_finally(f)).unwrap_or(0);
                    let catch_count: usize = catches.iter()
                        .map(|c| count_try_finally(&c.body))
                        .sum();
                    this + body_count + finally_count + catch_count
                }
                Expr_::Block(stmts) => stmts.iter().map(count_try_finally).sum(),
                Expr_::Let { init, body, .. } => {
                    count_try_finally(init) + count_try_finally(body)
                }
                Expr_::LetMut { init, body, .. } => {
                    count_try_finally(init) + count_try_finally(body)
                }
                Expr_::Match(scrutinee, arms) => {
                    count_try_finally(scrutinee) +
                    arms.iter().map(|a| {
                        count_try_finally(&a.body) +
                        a.guard.as_ref().map(|g| count_try_finally(g)).unwrap_or(0)
                    }).sum::<usize>()
                }
                Expr_::If(cond, then_branch, else_branch) => {
                    count_try_finally(cond) +
                    count_try_finally(then_branch) +
                    count_try_finally(else_branch)
                }
                Expr_::Lambda { body, .. } => count_try_finally(body),
                _ => 0,
            }
        }

        let try_count = count_try_finally(body);
        assert_eq!(try_count, 3, "Should have 3 Try-finally blocks for 3 defers, got {}", try_count);

        // Verify the outermost level is a Try with finally (from first defer)
        assert!(matches!(&body.value, Expr_::Try { finally: Some(_), .. }),
            "Top level should be Try-finally from first defer");
    }
}
