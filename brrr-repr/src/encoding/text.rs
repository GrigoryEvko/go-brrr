//! Text format encoder/decoder (.brrrx)
//!
//! S-expression based text format for human-readable representation of brrr-repr types.
//! Format follows Lisp-like syntax for easy parsing and readability.

use std::io::{Read, Write};

use lasso::{Key, Spur};

use crate::api::BrrrModule;
use crate::decl::FullDeclaration;
use crate::effects::{EffectOp, EffectRow};
use crate::error::ReprResult;
use crate::expr::{
    BinaryOp, CatchArm, Expr, Expr_, HandlerClause, HandlerDepth, Literal, MatchArm, Pattern,
    Pattern_, UnaryOp,
};
use crate::modes::Mode;
use crate::types::{
    BrrrType, EnumType, FieldType, FloatPrec, FuncType, InterfaceType, IntType, MethodParam,
    MethodSig, ModalKind, NumericType, ParamType, PrimKind, StructType, VariantType, WrapperKind,
};

/// Text format encoder
#[derive(Debug, Default)]
pub struct TextEncoder {
    _private: (),
}

impl TextEncoder {
    /// Create a new encoder
    pub fn new() -> Self {
        Self::default()
    }

    /// Encode a module to the writer
    pub fn encode<W: Write>(&self, module: &BrrrModule, mut writer: W) -> ReprResult<()> {
        // Write header
        writeln!(writer, "; brrr text format v{}", module.version)?;
        writeln!(writer, "(module \"{}\"", module.name)?;

        // Write files
        if !module.files.is_empty() {
            writeln!(writer, "  (files")?;
            for (i, file) in module.files.iter().enumerate() {
                writeln!(writer, "    ({} \"{}\")", i, escape_string(file))?;
            }
            writeln!(writer, "  )")?;
        }

        // Write types with proper serialization
        if !module.types.is_empty() {
            writeln!(writer, "  (types")?;
            for (i, ty) in module.types.iter().enumerate() {
                writeln!(writer, "    ({} {})", i, format_type(ty))?;
            }
            writeln!(writer, "  )")?;
        }

        // Write exprs with proper serialization
        if !module.exprs.is_empty() {
            writeln!(writer, "  (exprs")?;
            for (i, expr) in module.exprs.iter().enumerate() {
                writeln!(writer, "    ({} {})", i, format_expr(expr))?;
            }
            writeln!(writer, "  )")?;
        }

        // Write declarations
        if !module.declarations.is_empty() {
            writeln!(writer, "  (declarations")?;
            for (i, decl) in module.declarations.iter().enumerate() {
                let kind = declaration_kind_str(decl);
                writeln!(writer, "    ({} {})", i, kind)?;
            }
            writeln!(writer, "  )")?;
        }

        writeln!(writer, ")")?;

        Ok(())
    }
}

/// Get a string representation of the declaration kind
fn declaration_kind_str(decl: &FullDeclaration) -> &'static str {
    match decl {
        FullDeclaration::Function(_) => "function",
        FullDeclaration::Type(_) => "type",
        FullDeclaration::Trait(_) => "trait",
        FullDeclaration::Impl(_) => "impl",
        FullDeclaration::Const { .. } => "const",
        FullDeclaration::Static { .. } => "static",
        FullDeclaration::Module { .. } => "module",
        FullDeclaration::Use { .. } => "use",
        FullDeclaration::Extern { .. } => "extern",
    }
}

/// Text format decoder
#[derive(Debug, Default)]
pub struct TextDecoder {
    _private: (),
}

impl TextDecoder {
    /// Create a new decoder
    pub fn new() -> Self {
        Self::default()
    }

    /// Decode a module from the reader
    pub fn decode<R: Read>(&self, mut reader: R) -> ReprResult<BrrrModule> {
        use crate::error::DecodeError;

        let mut content = String::new();
        reader.read_to_string(&mut content)?;

        // Simple parsing - find module name
        let name = if let Some(start) = content.find("(module \"") {
            let rest = &content[start + 9..];
            if let Some(end) = rest.find('"') {
                rest[..end].to_string()
            } else {
                return Err(DecodeError::parse(1, 1, "missing module name closing quote").into());
            }
        } else {
            return Err(DecodeError::parse(1, 1, "missing module declaration").into());
        };

        // Extract version from header if present
        let version = if let Some(idx) = content.find("; brrr text format v") {
            let rest = &content[idx + 20..];
            rest.lines()
                .next()
                .and_then(|l| l.trim().parse().ok())
                .unwrap_or(1)
        } else {
            1
        };

        Ok(BrrrModule {
            name,
            files: Vec::new(),
            types: Vec::new(),
            exprs: Vec::new(),
            declarations: Vec::new(),
            version,
        })
    }
}

// ============================================================================
// Type Formatting
// ============================================================================

/// Format a BrrrType as an S-expression
pub fn format_type(ty: &BrrrType) -> String {
    match ty {
        BrrrType::Prim(kind) => format!("(prim {})", format_prim_kind(kind)),

        BrrrType::Numeric(num) => format!("(numeric {})", format_numeric(num)),

        BrrrType::Wrap(kind, inner) => {
            format!("(wrap {} {})", format_wrapper(kind), format_type(inner))
        }

        BrrrType::SizedArray(size, inner) => {
            format!("(sized-array {} {})", size, format_type(inner))
        }

        BrrrType::Modal(kind, inner) => {
            format!("(modal {} {})", format_modal(kind), format_type(inner))
        }

        BrrrType::Result(ok, err) => {
            format!("(result {} {})", format_type(ok), format_type(err))
        }

        BrrrType::Tuple(elems) => {
            if elems.is_empty() {
                "(tuple)".to_string()
            } else {
                let inner: Vec<String> = elems.iter().map(format_type).collect();
                format!("(tuple {})", inner.join(" "))
            }
        }

        BrrrType::Func(ft) => format!("(func {})", format_func_type(ft)),

        BrrrType::Var(v) => format!("(var {})", format_spur(v)),

        BrrrType::App(base, args) => {
            let args_str: Vec<String> = args.iter().map(format_type).collect();
            format!("(app {} ({}))", format_type(base), args_str.join(" "))
        }

        BrrrType::Named(name) => format!("(named {})", format_spur(name)),

        BrrrType::Struct(st) => format_struct_type(st),

        BrrrType::Enum(et) => format_enum_type(et),

        BrrrType::Interface(iface) => format_interface_type(iface),
    }
}

fn format_prim_kind(kind: &PrimKind) -> &'static str {
    kind.as_str()
}

fn format_numeric(num: &NumericType) -> &'static str {
    num.as_str()
}

fn format_wrapper(kind: &WrapperKind) -> &'static str {
    kind.as_str()
}

fn format_modal(kind: &ModalKind) -> String {
    kind.as_symbol()
}

fn format_func_type(ft: &FuncType) -> String {
    let params: Vec<String> = ft.params.iter().map(format_param_type).collect();
    let params_str = if params.is_empty() {
        "()".to_string()
    } else {
        format!("({})", params.join(" "))
    };

    let effects_str = format_effect_row(&ft.effects);
    let unsafe_str = if ft.is_unsafe { " unsafe" } else { "" };

    format!(
        "(params {}) (returns {}) (effects {}){unsafe_str}",
        params_str,
        format_type(&ft.return_type),
        effects_str
    )
}

fn format_param_type(param: &ParamType) -> String {
    let name_str = param
        .name
        .map(|s| format_spur(&s))
        .unwrap_or_else(|| "_".to_string());
    let mode_str = format_mode(&param.mode);
    format!("({} {} {})", name_str, format_type(&param.ty), mode_str)
}

fn format_mode(mode: &Mode) -> &'static str {
    mode.as_str()
}

fn format_effect_row(effects: &EffectRow) -> String {
    if effects.is_pure() {
        return "pure".to_string();
    }

    let ops: Vec<String> = effects.ops().iter().map(format_effect_op).collect();
    let ops_str = ops.join(" ");

    match effects.row_var() {
        Some(v) => format!("(row ({}) var:{})", ops_str, v.index()),
        None => format!("(row ({}))", ops_str),
    }
}

fn format_effect_op(op: &EffectOp) -> String {
    op.as_symbol()
}

fn format_struct_type(st: &StructType) -> String {
    let fields: Vec<String> = st.fields.iter().map(format_field_type).collect();
    let fields_str = if fields.is_empty() {
        String::new()
    } else {
        format!(" (fields {})", fields.join(" "))
    };
    format!(
        "(struct {} repr:{}{})",
        format_spur(&st.name),
        st.repr.as_str(),
        fields_str
    )
}

fn format_field_type(field: &FieldType) -> String {
    format!(
        "({} {} {})",
        format_spur(&field.name),
        format_type(&field.ty),
        field.vis.as_str()
    )
}

fn format_enum_type(et: &EnumType) -> String {
    let variants: Vec<String> = et.variants.iter().map(format_variant_type).collect();
    let variants_str = if variants.is_empty() {
        String::new()
    } else {
        format!(" (variants {})", variants.join(" "))
    };
    format!("(enum {}{})", format_spur(&et.name), variants_str)
}

fn format_variant_type(variant: &VariantType) -> String {
    if variant.fields.is_empty() {
        format!("({})", format_spur(&variant.name))
    } else {
        let fields: Vec<String> = variant.fields.iter().map(format_type).collect();
        format!("({} {})", format_spur(&variant.name), fields.join(" "))
    }
}

fn format_interface_type(iface: &InterfaceType) -> String {
    let methods: Vec<String> = iface.methods.iter().map(format_method_sig).collect();
    let methods_str = if methods.is_empty() {
        String::new()
    } else {
        format!(" (methods {})", methods.join(" "))
    };
    let embedded: Vec<String> = iface.embedded.iter().map(|e| format_spur(e)).collect();
    let embedded_str = if embedded.is_empty() {
        String::new()
    } else {
        format!(" (embedded {})", embedded.join(" "))
    };
    format!("(interface {}{}{})", format_spur(&iface.name), methods_str, embedded_str)
}

fn format_method_sig(method: &MethodSig) -> String {
    let params: Vec<String> = method.params.iter().map(format_method_param).collect();
    let params_str = if params.is_empty() {
        "()".to_string()
    } else {
        format!("({})", params.join(" "))
    };
    format!(
        "({} {} {})",
        format_spur(&method.name),
        params_str,
        format_type(&method.return_type)
    )
}

fn format_method_param(param: &MethodParam) -> String {
    let name_str = match param.name {
        Some(n) => format_spur(&n),
        None => "_".to_string(),
    };
    format!("({} {})", name_str, format_type(&param.ty))
}

// ============================================================================
// Expression Formatting
// ============================================================================

/// Format an Expr as an S-expression
pub fn format_expr(expr: &Expr) -> String {
    format_expr_inner(&expr.value)
}

fn format_expr_inner(expr: &Expr_) -> String {
    match expr {
        // === Literals and Variables ===
        Expr_::Lit(lit) => format_literal(lit),

        Expr_::Var(v) => format!("(var {})", format_spur(v)),

        Expr_::Global(g) => format!("(global {})", format_spur(g)),

        // === Operations ===
        Expr_::Unary(op, e) => format!("(unary {} {})", format_unop(op), format_expr(e)),

        Expr_::Binary(op, l, r) => {
            format!(
                "(binary {} {} {})",
                format_binop(op),
                format_expr(l),
                format_expr(r)
            )
        }

        Expr_::Call(f, args) => {
            let args_str: Vec<String> = args.iter().map(format_expr).collect();
            format!("(call {} ({}))", format_expr(f), args_str.join(" "))
        }

        Expr_::MethodCall(obj, method, args) => {
            let args_str: Vec<String> = args.iter().map(format_expr).collect();
            format!(
                "(method {} {} ({}))",
                format_expr(obj),
                format_spur(method),
                args_str.join(" ")
            )
        }

        // === Data Construction ===
        Expr_::Tuple(elems) => {
            let elems_str: Vec<String> = elems.iter().map(format_expr).collect();
            format!("(tuple {})", elems_str.join(" "))
        }

        Expr_::Array(elems) => {
            let elems_str: Vec<String> = elems.iter().map(format_expr).collect();
            format!("(array {})", elems_str.join(" "))
        }

        Expr_::Struct { name, fields } => {
            let fields_str: Vec<String> = fields
                .iter()
                .map(|(n, e)| format!("({} {})", format_spur(n), format_expr(e)))
                .collect();
            format!("(struct {} ({}))", format_spur(name), fields_str.join(" "))
        }

        Expr_::Variant {
            type_name,
            variant,
            fields,
        } => {
            let fields_str: Vec<String> = fields.iter().map(format_expr).collect();
            format!(
                "(variant {} {} ({}))",
                format_spur(type_name),
                format_spur(variant),
                fields_str.join(" ")
            )
        }

        // === Data Access ===
        Expr_::Field(base, field) => {
            format!("(field {} {})", format_expr(base), format_spur(field))
        }

        Expr_::Index(base, index) => {
            format!("(index {} {})", format_expr(base), format_expr(index))
        }

        Expr_::TupleProj(base, idx) => {
            format!("(tuple-proj {} {})", format_expr(base), idx)
        }

        // === Control Flow ===
        Expr_::If(cond, then_branch, else_branch) => {
            format!(
                "(if {} {} {})",
                format_expr(cond),
                format_expr(then_branch),
                format_expr(else_branch)
            )
        }

        Expr_::Match(scrutinee, arms) => {
            let arms_str: Vec<String> = arms.iter().map(format_match_arm).collect();
            format!("(match {} ({}))", format_expr(scrutinee), arms_str.join(" "))
        }

        Expr_::Loop { label, body } => {
            let label_str = label
                .map(|l| format!(" label:{}", format_spur(&l)))
                .unwrap_or_default();
            format!("(loop{} {})", label_str, format_expr(body))
        }

        Expr_::While { label, cond, body } => {
            let label_str = label
                .map(|l| format!(" label:{}", format_spur(&l)))
                .unwrap_or_default();
            format!(
                "(while{} {} {})",
                label_str,
                format_expr(cond),
                format_expr(body)
            )
        }

        Expr_::For {
            label,
            var,
            iter,
            body,
        } => {
            let label_str = label
                .map(|l| format!(" label:{}", format_spur(&l)))
                .unwrap_or_default();
            format!(
                "(for{} {} {} {})",
                label_str,
                format_spur(var),
                format_expr(iter),
                format_expr(body)
            )
        }

        Expr_::Break { label, value } => {
            let label_str = label
                .map(|l| format!(" label:{}", format_spur(&l)))
                .unwrap_or_default();
            let value_str = value
                .as_ref()
                .map(|v| format!(" {}", format_expr(v)))
                .unwrap_or_default();
            format!("(break{}{})", label_str, value_str)
        }

        Expr_::Continue { label } => {
            let label_str = label
                .map(|l| format!(" label:{}", format_spur(&l)))
                .unwrap_or_default();
            format!("(continue{})", label_str)
        }

        Expr_::Return(value) => match value {
            Some(v) => format!("(return {})", format_expr(v)),
            None => "(return)".to_string(),
        },

        // === Bindings ===
        Expr_::Let {
            pattern,
            ty,
            init,
            body,
        } => {
            let ty_str = ty
                .as_ref()
                .map(|t| format!(" : {}", format_type(t)))
                .unwrap_or_default();
            format!(
                "(let {}{} {} {})",
                format_pattern(pattern),
                ty_str,
                format_expr(init),
                format_expr(body)
            )
        }

        Expr_::LetMut {
            var,
            ty,
            init,
            body,
        } => {
            let ty_str = ty
                .as_ref()
                .map(|t| format!(" : {}", format_type(t)))
                .unwrap_or_default();
            format!(
                "(let-mut {}{} {} {})",
                format_spur(var),
                ty_str,
                format_expr(init),
                format_expr(body)
            )
        }

        Expr_::Assign(lhs, rhs) => {
            format!("(assign {} {})", format_expr(lhs), format_expr(rhs))
        }

        // === Functions ===
        Expr_::Lambda { params, body } => {
            let params_str: Vec<String> = params
                .iter()
                .map(|(v, t)| format!("({} {})", format_spur(v), format_type(t)))
                .collect();
            format!("(lambda ({}) {})", params_str.join(" "), format_expr(body))
        }

        Expr_::Closure {
            params,
            captures,
            body,
        } => {
            let params_str: Vec<String> = params
                .iter()
                .map(|(v, t)| format!("({} {})", format_spur(v), format_type(t)))
                .collect();
            let captures_str: Vec<String> = captures.iter().map(format_spur).collect();
            format!(
                "(closure ({}) captures:({}) {})",
                params_str.join(" "),
                captures_str.join(" "),
                format_expr(body)
            )
        }

        // === Memory Operations ===
        Expr_::Box(e) => format!("(box {})", format_expr(e)),
        Expr_::Deref(e) => format!("(deref {})", format_expr(e)),
        Expr_::Borrow(e) => format!("(borrow {})", format_expr(e)),
        Expr_::BorrowMut(e) => format!("(borrow-mut {})", format_expr(e)),
        Expr_::Move(e) => format!("(move {})", format_expr(e)),
        Expr_::Drop(e) => format!("(drop {})", format_expr(e)),

        // === Exception Handling ===
        Expr_::Throw(e) => format!("(throw {})", format_expr(e)),

        Expr_::Try {
            body,
            catches,
            finally,
        } => {
            let catches_str: Vec<String> = catches.iter().map(format_catch_arm).collect();
            let finally_str = finally
                .as_ref()
                .map(|f| format!(" finally:{}", format_expr(f)))
                .unwrap_or_default();
            format!(
                "(try {} ({}){})",
                format_expr(body),
                catches_str.join(" "),
                finally_str
            )
        }

        // === Async/Concurrency ===
        Expr_::Await(e) => format!("(await {})", format_expr(e)),
        Expr_::Yield(e) => format!("(yield {})", format_expr(e)),
        Expr_::Async(e) => format!("(async {})", format_expr(e)),
        Expr_::Spawn(e) => format!("(spawn {})", format_expr(e)),

        // === Effect Operations ===
        Expr_::Handle(body, handler) => {
            let clauses_str: Vec<String> =
                handler.clauses.iter().map(format_handler_clause).collect();
            let return_str = handler
                .return_clause
                .as_ref()
                .map(|(v, e)| format!(" return:({} {})", format_spur(v), format_expr(e)))
                .unwrap_or_default();
            let depth_str = match handler.depth {
                HandlerDepth::Shallow => "",
                HandlerDepth::Deep => " deep",
            };
            format!(
                "(handle {} ({}){}{})",
                format_expr(body),
                clauses_str.join(" "),
                return_str,
                depth_str
            )
        }

        Expr_::Perform(op, args) => {
            let args_str: Vec<String> = args.iter().map(format_expr).collect();
            format!("(perform {} ({}))", format_effect_op(op), args_str.join(" "))
        }

        Expr_::Resume { var, value } => {
            format!("(resume {} {})", format_spur(var), format_expr(value))
        }

        // === Delimited Continuations ===
        Expr_::Reset { label, body } => {
            format!("(reset {} {})", format_spur(label), format_expr(body))
        }

        Expr_::Shift { label, var, body } => {
            format!(
                "(shift {} {} {})",
                format_spur(label),
                format_spur(var),
                format_expr(body)
            )
        }

        // === Type Operations ===
        Expr_::As(e, ty) => format!("(as {} {})", format_expr(e), format_type(ty)),
        Expr_::Is(e, ty) => format!("(is {} {})", format_expr(e), format_type(ty)),
        Expr_::Sizeof(ty) => format!("(sizeof {})", format_type(ty)),
        Expr_::Alignof(ty) => format!("(alignof {})", format_type(ty)),

        // === Blocks ===
        Expr_::Block(stmts) => {
            let stmts_str: Vec<String> = stmts.iter().map(format_expr).collect();
            format!("(block {})", stmts_str.join(" "))
        }

        Expr_::Seq(first, second) => {
            format!("(seq {} {})", format_expr(first), format_expr(second))
        }

        Expr_::Unsafe(e) => format!("(unsafe {})", format_expr(e)),

        // === Special ===
        Expr_::Hole => "(hole)".to_string(),
        Expr_::Error(msg) => format!("(error {})", format_spur(msg)),

        // === Gradual Typing ===
        Expr_::GradualCast {
            expr,
            from,
            to,
            kind,
            blame,
        } => {
            format!(
                "(gradual-cast {} from:{:?} to:{:?} kind:{} blame:{})",
                format_expr(expr),
                from,
                to,
                kind,
                blame
            )
        }

        // === Control Flow Labels ===
        Expr_::Goto { label } => format!("(goto {})", format_spur(label)),
        Expr_::Labeled { label, body } => {
            format!("(labeled {} {})", format_spur(label), format_expr(body))
        }
    }
}

fn format_match_arm(arm: &MatchArm) -> String {
    let guard_str = arm
        .guard
        .as_ref()
        .map(|g| format!(" if:{}", format_expr(g)))
        .unwrap_or_default();
    format!(
        "(arm {}{} {})",
        format_pattern(&arm.pattern),
        guard_str,
        format_expr(&arm.body)
    )
}

fn format_catch_arm(arm: &CatchArm) -> String {
    format!(
        "(catch {} {} {})",
        format_pattern(&arm.pattern),
        format_type(&arm.exception_type),
        format_expr(&arm.body)
    )
}

fn format_handler_clause(clause: &HandlerClause) -> String {
    let params_str: Vec<String> = clause.params.iter().map(format_spur).collect();
    let linearity = if clause.continuation_linearity.is_one_shot() {
        "one-shot"
    } else {
        "multi-shot"
    };
    format!(
        "(clause {} ({}) cont:{} {} {})",
        format_effect_op(&clause.op),
        params_str.join(" "),
        format_spur(&clause.continuation),
        linearity,
        format_expr(&clause.body)
    )
}

// ============================================================================
// Literal Formatting
// ============================================================================

fn format_literal(lit: &Literal) -> String {
    match lit {
        Literal::Unit => "(lit unit)".to_string(),
        Literal::Bool(b) => format!("(lit bool {})", b),
        Literal::Int(v, ty) => format!("(lit int {} {})", v, ty.as_str()),
        Literal::Float(bits, prec) => {
            let value = match prec {
                FloatPrec::F16 | FloatPrec::F32 => bits.to_f32() as f64,
                FloatPrec::F64 => bits.to_f64(),
            };
            format!("(lit float {} {})", value, prec.as_str())
        }
        Literal::String(s) => format!("(lit string \"{}\")", escape_string(s)),
        Literal::Char(c) => format!("(lit char '{}')", escape_char(*c)),
    }
}

// ============================================================================
// Pattern Formatting
// ============================================================================

/// Format a Pattern as an S-expression
pub fn format_pattern(pat: &Pattern) -> String {
    format_pattern_inner(&pat.value)
}

fn format_pattern_inner(pat: &Pattern_) -> String {
    match pat {
        Pattern_::Wild => "(pat wild)".to_string(),

        Pattern_::Var(v) => format!("(pat var {})", format_spur(v)),

        Pattern_::Lit(lit) => format!("(pat lit {})", format_literal(lit)),

        Pattern_::Tuple(pats) => {
            let pats_str: Vec<String> = pats.iter().map(format_pattern).collect();
            format!("(pat tuple {})", pats_str.join(" "))
        }

        Pattern_::Struct { name, fields } => {
            let fields_str: Vec<String> = fields
                .iter()
                .map(|(n, p)| format!("({} {})", format_spur(n), format_pattern(p)))
                .collect();
            format!(
                "(pat struct {} ({}))",
                format_spur(name),
                fields_str.join(" ")
            )
        }

        Pattern_::Variant {
            type_name,
            variant,
            fields,
        } => {
            let fields_str: Vec<String> = fields.iter().map(format_pattern).collect();
            format!(
                "(pat variant {} {} ({}))",
                format_spur(type_name),
                format_spur(variant),
                fields_str.join(" ")
            )
        }

        Pattern_::Or(l, r) => format!("(pat or {} {})", format_pattern(l), format_pattern(r)),

        Pattern_::Guard(p, e) => format!("(pat guard {} {})", format_pattern(p), format_expr(e)),

        Pattern_::Ref(p) => format!("(pat ref {})", format_pattern(p)),

        Pattern_::Box(p) => format!("(pat box {})", format_pattern(p)),

        Pattern_::Rest(binding) => match binding {
            Some(v) => format!("(pat rest {})", format_spur(v)),
            None => "(pat rest)".to_string(),
        },

        Pattern_::As(p, binding) => {
            format!("(pat as {} {})", format_pattern(p), format_spur(binding))
        }

        Pattern_::Type { expected, binding } => match binding {
            Some(v) => format!("(pat type {} {})", format_type(expected), format_spur(v)),
            None => format!("(pat type {})", format_type(expected)),
        },
    }
}

// ============================================================================
// Operator Formatting
// ============================================================================

fn format_unop(op: &UnaryOp) -> &'static str {
    op.as_str()
}

fn format_binop(op: &BinaryOp) -> &'static str {
    op.as_str()
}

// ============================================================================
// Utility Functions
// ============================================================================

/// Format a Spur (interned string identifier) as a numeric ID
fn format_spur(spur: &Spur) -> String {
    format!("id:{}", spur.into_usize())
}

/// Escape special characters in strings for S-expression output
fn escape_string(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t")
}

/// Escape special characters in chars for S-expression output
fn escape_char(c: char) -> String {
    match c {
        '\'' => "\\'".to_string(),
        '\\' => "\\\\".to_string(),
        '\n' => "\\n".to_string(),
        '\r' => "\\r".to_string(),
        '\t' => "\\t".to_string(),
        c if c.is_control() => format!("\\u{{{:04x}}}", c as u32),
        c => c.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::WithLoc;

    #[test]
    fn test_format_prim_types() {
        assert_eq!(format_type(&BrrrType::UNIT), "(prim Unit)");
        assert_eq!(format_type(&BrrrType::BOOL), "(prim Bool)");
        assert_eq!(format_type(&BrrrType::STRING), "(prim String)");
        assert_eq!(format_type(&BrrrType::NEVER), "(prim Never)");
    }

    #[test]
    fn test_format_numeric_types() {
        assert_eq!(
            format_type(&BrrrType::Numeric(NumericType::Int(IntType::I32))),
            "(numeric i32)"
        );
        assert_eq!(
            format_type(&BrrrType::Numeric(NumericType::Float(FloatPrec::F64))),
            "(numeric f64)"
        );
    }

    #[test]
    fn test_format_wrapper_types() {
        let inner = BrrrType::BOOL;
        assert_eq!(
            format_type(&BrrrType::Wrap(WrapperKind::Array, Box::new(inner.clone()))),
            "(wrap Array (prim Bool))"
        );
        assert_eq!(
            format_type(&BrrrType::Wrap(WrapperKind::Option, Box::new(inner.clone()))),
            "(wrap Option (prim Bool))"
        );
    }

    #[test]
    fn test_format_result_type() {
        let ok = BrrrType::Numeric(NumericType::Int(IntType::I32));
        let err = BrrrType::STRING;
        assert_eq!(
            format_type(&BrrrType::Result(Box::new(ok), Box::new(err))),
            "(result (numeric i32) (prim String))"
        );
    }

    #[test]
    fn test_format_tuple_type() {
        let elems = vec![
            BrrrType::BOOL,
            BrrrType::Numeric(NumericType::Int(IntType::I32)),
        ];
        assert_eq!(
            format_type(&BrrrType::Tuple(elems)),
            "(tuple (prim Bool) (numeric i32))"
        );
    }

    #[test]
    fn test_format_literal_expr() {
        let unit_expr = WithLoc::synthetic(Expr_::Lit(Literal::Unit));
        assert_eq!(format_expr(&unit_expr), "(lit unit)");

        let int_expr = WithLoc::synthetic(Expr_::Lit(Literal::i32(42)));
        assert_eq!(format_expr(&int_expr), "(lit int 42 i32)");

        let bool_expr = WithLoc::synthetic(Expr_::Lit(Literal::Bool(true)));
        assert_eq!(format_expr(&bool_expr), "(lit bool true)");

        let string_expr = WithLoc::synthetic(Expr_::Lit(Literal::String("hello".to_string())));
        assert_eq!(format_expr(&string_expr), "(lit string \"hello\")");
    }

    #[test]
    fn test_format_binary_expr() {
        let left = WithLoc::synthetic(Expr_::Lit(Literal::i32(1)));
        let right = WithLoc::synthetic(Expr_::Lit(Literal::i32(2)));
        let binary = WithLoc::synthetic(Expr_::Binary(
            BinaryOp::Add,
            Box::new(left),
            Box::new(right),
        ));
        assert_eq!(
            format_expr(&binary),
            "(binary add (lit int 1 i32) (lit int 2 i32))"
        );
    }

    #[test]
    fn test_format_if_expr() {
        let cond = WithLoc::synthetic(Expr_::Lit(Literal::Bool(true)));
        let then_branch = WithLoc::synthetic(Expr_::Lit(Literal::i32(1)));
        let else_branch = WithLoc::synthetic(Expr_::Lit(Literal::i32(2)));
        let if_expr = WithLoc::synthetic(Expr_::If(
            Box::new(cond),
            Box::new(then_branch),
            Box::new(else_branch),
        ));
        assert_eq!(
            format_expr(&if_expr),
            "(if (lit bool true) (lit int 1 i32) (lit int 2 i32))"
        );
    }

    #[test]
    fn test_format_pattern() {
        let wild = WithLoc::synthetic(Pattern_::Wild);
        assert_eq!(format_pattern(&wild), "(pat wild)");

        let lit_pat = WithLoc::synthetic(Pattern_::Lit(Literal::i32(42)));
        assert_eq!(format_pattern(&lit_pat), "(pat lit (lit int 42 i32))");
    }

    #[test]
    fn test_escape_string() {
        assert_eq!(escape_string("hello"), "hello");
        assert_eq!(escape_string("hello\nworld"), "hello\\nworld");
        assert_eq!(escape_string("say \"hi\""), "say \\\"hi\\\"");
        assert_eq!(escape_string("back\\slash"), "back\\\\slash");
    }

    #[test]
    fn test_escape_char() {
        assert_eq!(escape_char('a'), "a");
        assert_eq!(escape_char('\''), "\\'");
        assert_eq!(escape_char('\n'), "\\n");
        assert_eq!(escape_char('\t'), "\\t");
    }

    #[test]
    fn test_encoder_output() {
        let encoder = TextEncoder::new();
        let module = BrrrModule {
            name: "test_module".to_string(),
            files: vec!["file1.brrr".to_string()],
            types: vec![BrrrType::BOOL],
            exprs: vec![WithLoc::synthetic(Expr_::Lit(Literal::i32(42)))],
            declarations: vec![],
            version: 1,
        };

        let mut output = Vec::new();
        encoder.encode(&module, &mut output).unwrap();
        let output_str = String::from_utf8(output).unwrap();

        assert!(output_str.contains("(module \"test_module\""));
        assert!(output_str.contains("(prim Bool)"));
        assert!(output_str.contains("(lit int 42 i32)"));
    }
}
