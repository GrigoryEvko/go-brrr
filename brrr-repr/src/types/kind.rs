//! Kind system for higher-kinded types
//!
//! Mirrors F* Kinds.fsti:
//! ```fstar
//! type kind =
//!   | KStar   : kind                    (* * - proper types *)
//!   | KArrow  : kind -> kind -> kind    (* k1 -> k2 - type constructor *)
//!   | KRow    : kind                    (* Row - effect row kind *)
//!   | KRegion : kind                    (* Region - lifetime kind *)
//! ```

use serde::{Deserialize, Serialize};

/// Kind - classifies types in the type system hierarchy
///
/// Kinds prevent ill-formed type applications like `Int<Bool>`.
/// Only types of kind `* -> *` can be applied to types of kind `*`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Kind {
    /// `*` - proper types (Int, Bool, String, etc.)
    /// These are types that can have values.
    Star,

    /// `k1 -> k2` - type constructor kinds
    /// Example: `Option : * -> *`, `Result : * -> * -> *`
    Arrow(Box<Kind>, Box<Kind>),

    /// `Row` - effect row kind
    /// Used for effect type variables in the effect system.
    Row,

    /// `Region` - lifetime/region kind
    /// Used for region polymorphism in borrow checking.
    Region,
}

impl Kind {
    /// Type kind `*` - the kind of proper types
    pub const TYPE: Self = Self::Star;

    /// Effect row kind - for effect polymorphism
    pub const EFFECT: Self = Self::Row;

    /// Region kind - for lifetime polymorphism
    pub const LIFETIME: Self = Self::Region;

    /// Create an arrow kind `k1 -> k2`
    #[must_use]
    pub fn arrow(from: Self, to: Self) -> Self {
        Self::Arrow(Box::new(from), Box::new(to))
    }

    /// `* -> *` - unary type constructors (Option, Vec, Box, etc.)
    #[must_use]
    pub fn type_to_type() -> Self {
        Self::arrow(Self::Star, Self::Star)
    }

    /// `* -> * -> *` - binary type constructors (Result, Map, Either, etc.)
    #[must_use]
    pub fn type2_to_type() -> Self {
        Self::arrow(Self::Star, Self::type_to_type())
    }

    /// `* -> * -> * -> *` - ternary type constructors
    #[must_use]
    pub fn type3_to_type() -> Self {
        Self::arrow(Self::Star, Self::type2_to_type())
    }

    /// `Row -> *` - effect-parameterized type
    #[must_use]
    pub fn effect_to_type() -> Self {
        Self::arrow(Self::Row, Self::Star)
    }

    /// `Region -> *` - region-parameterized type
    #[must_use]
    pub fn region_to_type() -> Self {
        Self::arrow(Self::Region, Self::Star)
    }

    /// Get arity (number of arrow arguments before reaching a base kind)
    #[must_use]
    pub fn arity(&self) -> usize {
        match self {
            Self::Arrow(_, to) => 1 + to.arity(),
            Self::Star | Self::Row | Self::Region => 0,
        }
    }

    /// Get the result kind after applying all arguments
    #[must_use]
    pub fn result(&self) -> &Self {
        match self {
            Self::Arrow(_, to) => to.result(),
            k => k,
        }
    }

    /// Check if this is a proper type kind (`*`)
    #[must_use]
    pub const fn is_type(&self) -> bool {
        matches!(self, Self::Star)
    }

    /// Check if this is an effect row kind
    #[must_use]
    pub const fn is_effect(&self) -> bool {
        matches!(self, Self::Row)
    }

    /// Check if this is a region kind
    #[must_use]
    pub const fn is_region(&self) -> bool {
        matches!(self, Self::Region)
    }

    /// Check if this is a type constructor kind (`k -> ...`)
    #[must_use]
    pub const fn is_constructor(&self) -> bool {
        matches!(self, Self::Arrow(_, _))
    }

    /// Apply one type argument, returning the resulting kind
    /// Returns `None` if this kind doesn't accept arguments.
    #[must_use]
    pub fn apply(&self) -> Option<&Self> {
        match self {
            Self::Arrow(_, to) => Some(to),
            _ => None,
        }
    }

    /// Apply one type argument, checking kind compatibility
    /// Returns `None` if the argument kind doesn't match.
    #[must_use]
    pub fn apply_checked(&self, arg_kind: &Self) -> Option<&Self> {
        match self {
            Self::Arrow(expected, result) if expected.as_ref() == arg_kind => Some(result),
            _ => None,
        }
    }

    /// Get the expected argument kind for application
    /// Returns `None` if this kind doesn't accept arguments.
    #[must_use]
    pub fn argument_kind(&self) -> Option<&Self> {
        match self {
            Self::Arrow(from, _) => Some(from),
            _ => None,
        }
    }

    /// Format kind using standard notation
    /// `*`, `* -> *`, `Row`, `Region`
    #[must_use]
    pub fn format(&self) -> String {
        match self {
            Self::Star => "*".to_string(),
            Self::Row => "Row".to_string(),
            Self::Region => "Region".to_string(),
            Self::Arrow(from, to) => {
                let from_str = match from.as_ref() {
                    Self::Arrow(_, _) => format!("({})", from.format()),
                    _ => from.format(),
                };
                format!("{} -> {}", from_str, to.format())
            }
        }
    }
}

impl Default for Kind {
    fn default() -> Self {
        Self::Star
    }
}

impl std::fmt::Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.format())
    }
}

/// A type variable paired with its kind annotation
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct KindedVar {
    /// The type variable identifier
    pub var: super::TypeVar,
    /// The kind of this variable
    pub kind: Kind,
}

impl KindedVar {
    /// Create a type variable with kind `*`
    #[must_use]
    pub fn of_type(var: super::TypeVar) -> Self {
        Self {
            var,
            kind: Kind::Star,
        }
    }

    /// Create a type variable with given kind
    #[must_use]
    pub fn new(var: super::TypeVar, kind: Kind) -> Self {
        Self { var, kind }
    }

    /// Create a type constructor variable (`* -> *`)
    #[must_use]
    pub fn type_constructor(var: super::TypeVar) -> Self {
        Self {
            var,
            kind: Kind::type_to_type(),
        }
    }
}

/// Kind context - maps type variables to their kinds
pub type KindCtx = Vec<KindedVar>;

/// Look up the kind of a type variable in a context
#[must_use]
pub fn lookup_kind<'a>(var: &super::TypeVar, ctx: &'a KindCtx) -> Option<&'a Kind> {
    ctx.iter().find(|kv| &kv.var == var).map(|kv| &kv.kind)
}

/// Extend a kind context with a new binding
pub fn extend_kind_ctx(ctx: &mut KindCtx, var: super::TypeVar, kind: Kind) {
    ctx.push(KindedVar { var, kind });
}

/// Check if a kind is well-formed (all base kinds are valid)
/// This is trivially true for our kind system since all constructors are valid.
#[must_use]
#[allow(dead_code)] // API completeness - validates kind structures
pub const fn is_well_formed(_kind: &Kind) -> bool {
    true
}

// ============================================================================
// Named Kind Environment - Maps named types to their kinds
// ============================================================================

use std::collections::HashMap;
use super::{BrrrType, TypeName};

/// Named kind environment - maps type names to their kinds.
///
/// Mirrors F* `type named_kind_env = list (type_name & kind)`.
pub type NamedKindEnv = HashMap<TypeName, Kind>;

/// Creates the default named kind environment with standard type constructors.
///
/// Mirrors F* `default_named_kind_env` which includes:
/// - Effect row types (IO, Pure, Async, etc.) with `KRow`
/// - Region types (Static) with `KRegion`
/// - Unary type constructors (Option, Vec, Box, etc.) with `* -> *`
/// - Binary type constructors (Result, Map, Either, etc.) with `* -> * -> *`
/// - Higher-kinded type constructors (Functor, Monad, etc.) with `(* -> *) -> *`
///
/// NOTE: This function requires an interner to create the type names.
/// Use `default_kind_env_with_interner` if you have access to one.
#[must_use]
pub fn default_kind_env_entries() -> Vec<(&'static str, Kind)> {
    vec![
        // ========================================================================
        // EFFECT ROW TYPES (KRow)
        // ========================================================================
        ("IO", Kind::Row),
        ("Pure", Kind::Row),
        ("Async", Kind::Row),
        ("State", Kind::Row),
        ("Error", Kind::Row),
        ("Reader", Kind::Row),
        ("Writer", Kind::Row),
        ("Console", Kind::Row),
        ("Network", Kind::Row),
        ("FileSystem", Kind::Row),
        ("Random", Kind::Row),
        ("Unsafe", Kind::Row),
        // Effect row combinator: Eff : Row -> * -> *
        ("Eff", Kind::arrow(Kind::Row, Kind::type_to_type())),
        // ========================================================================
        // REGION/LIFETIME TYPES (KRegion)
        // ========================================================================
        ("Static", Kind::Region),
        // Region-parameterized types: Region -> * -> *
        ("RegionRef", Kind::arrow(Kind::Region, Kind::type_to_type())),
        ("RegionRefMut", Kind::arrow(Kind::Region, Kind::type_to_type())),
        ("RegionBox", Kind::arrow(Kind::Region, Kind::type_to_type())),
        // ========================================================================
        // STANDARD TYPE CONSTRUCTORS (* -> *)
        // ========================================================================
        ("Option", Kind::type_to_type()),
        ("Vec", Kind::type_to_type()),
        ("List", Kind::type_to_type()),
        ("Set", Kind::type_to_type()),
        ("Box", Kind::type_to_type()),
        ("Rc", Kind::type_to_type()),
        ("Arc", Kind::type_to_type()),
        ("Ref", Kind::type_to_type()),
        ("Future", Kind::type_to_type()),
        ("Promise", Kind::type_to_type()),
        ("Iterator", Kind::type_to_type()),
        ("Stream", Kind::type_to_type()),
        ("Cell", Kind::type_to_type()),
        ("RefCell", Kind::type_to_type()),
        ("Mutex", Kind::type_to_type()),
        ("RwLock", Kind::type_to_type()),
        // ========================================================================
        // BINARY TYPE CONSTRUCTORS (* -> * -> *)
        // ========================================================================
        ("Result", Kind::type2_to_type()),
        ("Map", Kind::type2_to_type()),
        ("HashMap", Kind::type2_to_type()),
        ("BTreeMap", Kind::type2_to_type()),
        ("Either", Kind::type2_to_type()),
        ("Pair", Kind::type2_to_type()),
        // ========================================================================
        // HIGHER-KINDED TYPE CONSTRUCTORS ((* -> *) -> *)
        // ========================================================================
        // Type-class-like constraints that take a type constructor
        ("Functor", Kind::arrow(Kind::type_to_type(), Kind::Star)),
        ("Applicative", Kind::arrow(Kind::type_to_type(), Kind::Star)),
        ("Monad", Kind::arrow(Kind::type_to_type(), Kind::Star)),
        ("Foldable", Kind::arrow(Kind::type_to_type(), Kind::Star)),
        ("Traversable", Kind::arrow(Kind::type_to_type(), Kind::Star)),
        // ========================================================================
        // BIFUNCTORS ((* -> * -> *) -> *)
        // ========================================================================
        ("Bifunctor", Kind::arrow(Kind::type2_to_type(), Kind::Star)),
    ]
}

/// Creates a default named kind environment using the provided interner.
///
/// # Arguments
/// * `intern` - A closure that interns a string and returns a `TypeName` (Spur)
#[must_use]
pub fn default_kind_env<F>(mut intern: F) -> NamedKindEnv
where
    F: FnMut(&str) -> TypeName,
{
    let entries = default_kind_env_entries();
    let mut env = HashMap::with_capacity(entries.len());
    for (name, kind) in entries {
        env.insert(intern(name), kind);
    }
    env
}

// ============================================================================
// Kind Inference - Infer the kind of a BrrrType
// ============================================================================

/// Infers the kind of a type given a named kind environment and kind context.
///
/// Mirrors F* `infer_kind_env : named_kind_env -> kind_ctx -> brrr_type -> option kind`.
///
/// # Kind Inference Rules
/// - `Prim(_)` -> `*` (primitive types are proper types)
/// - `Numeric(_)` -> `*` (numeric types are proper types)
/// - `Wrap(_, inner)` -> `*` if inner has kind `*`
/// - `Modal(_, inner)` -> `*` if inner has kind `*`
/// - `Result(ok, err)` -> `*` if both have kind `*`
/// - `Tuple(ts)` -> `*` if all elements have kind `*`
/// - `Func(ft)` -> `*` if all params and return have kind `*`
/// - `Var(v)` -> lookup in kind context
/// - `App(f, args)` -> apply arrow kinds
/// - `Named(n)` -> lookup in named kind environment
/// - `Struct(_)` / `Enum(_)` -> lookup in env, fallback to `*`
#[must_use]
pub fn infer_kind(env: &NamedKindEnv, ctx: &KindCtx, ty: &BrrrType) -> Option<Kind> {
    match ty {
        // Primitive types: all have kind *
        BrrrType::Prim(_) => Some(Kind::Star),

        // Numeric types: all have kind *
        BrrrType::Numeric(_) => Some(Kind::Star),

        // Wrapper types: inner must be *, result is *
        BrrrType::Wrap(_, inner) => match infer_kind(env, ctx, inner) {
            Some(Kind::Star) => Some(Kind::Star),
            _ => None,
        },

        // Sized arrays: element must be *, result is *
        BrrrType::SizedArray(_, inner) => match infer_kind(env, ctx, inner) {
            Some(Kind::Star) => Some(Kind::Star),
            _ => None,
        },

        // Modal types: inner must be *, result is *
        BrrrType::Modal(_, inner) => match infer_kind(env, ctx, inner) {
            Some(Kind::Star) => Some(Kind::Star),
            _ => None,
        },

        // Result T E: both T and E must have kind *
        BrrrType::Result(t_ok, t_err) => {
            match (infer_kind(env, ctx, t_ok), infer_kind(env, ctx, t_err)) {
                (Some(Kind::Star), Some(Kind::Star)) => Some(Kind::Star),
                _ => None,
            }
        }

        // Tuple: all elements must have kind *
        BrrrType::Tuple(ts) => {
            if infer_kind_list(env, ctx, ts) {
                Some(Kind::Star)
            } else {
                None
            }
        }

        // Function types: all param types and return type must have kind *
        BrrrType::Func(ft) => {
            let params_ok = ft.params.iter().all(|p| {
                matches!(infer_kind(env, ctx, &p.ty), Some(Kind::Star))
            });
            let return_ok = matches!(infer_kind(env, ctx, &ft.return_type), Some(Kind::Star));
            if params_ok && return_ok {
                Some(Kind::Star)
            } else {
                None
            }
        }

        // Type variable: lookup in kind context
        BrrrType::Var(v) => lookup_kind(v, ctx).cloned(),

        // Type application: F<args> where F has kind k1 -> k2 -> ... -> kN -> *
        BrrrType::App(f, args) => match infer_kind(env, ctx, f) {
            Some(fk) => infer_kind_app(env, ctx, &fk, args),
            None => None,
        },

        // Named types: lookup in named kind environment
        BrrrType::Named(name) => env.get(name).cloned(),

        // Struct: lookup by struct name in named kind environment.
        // Fallback to * for unregistered structs (permissive mode).
        BrrrType::Struct(st) => match env.get(&st.name) {
            Some(k) => Some(k.clone()),
            None => Some(Kind::Star), // Permissive: assume unregistered structs have kind *
        },

        // Enum: lookup by enum name in named kind environment.
        // Fallback to * for unregistered enums (permissive mode).
        BrrrType::Enum(et) => match env.get(&et.name) {
            Some(k) => Some(k.clone()),
            None => Some(Kind::Star), // Permissive: assume unregistered enums have kind *
        },

        // Interface: lookup by interface name in named kind environment.
        // Fallback to * for unregistered interfaces (permissive mode).
        BrrrType::Interface(it) => match env.get(&it.name) {
            Some(k) => Some(k.clone()),
            None => Some(Kind::Star), // Permissive: assume unregistered interfaces have kind *
        },
    }
}

/// Helper: check that all types in a list have kind *.
#[must_use]
fn infer_kind_list(env: &NamedKindEnv, ctx: &KindCtx, ts: &[BrrrType]) -> bool {
    ts.iter()
        .all(|t| matches!(infer_kind(env, ctx, t), Some(Kind::Star)))
}

/// Helper: apply type arguments to a function kind.
///
/// If F has kind `k1 -> (k2 -> k)`, and we apply arg of kind k1,
/// we get kind `k2 -> k`.
#[must_use]
fn infer_kind_app(
    env: &NamedKindEnv,
    ctx: &KindCtx,
    fk: &Kind,
    args: &[BrrrType],
) -> Option<Kind> {
    if args.is_empty() {
        return Some(fk.clone());
    }

    match fk {
        Kind::Arrow(k_param, k_result) => {
            let arg = &args[0];
            match infer_kind(env, ctx, arg) {
                Some(ref k_arg) if k_arg == k_param.as_ref() => {
                    infer_kind_app(env, ctx, k_result, &args[1..])
                }
                _ => None,
            }
        }
        _ => None, // Not a function kind, but we have arguments
    }
}

// ============================================================================
// Kind Checking - Check that a type has a specific kind
// ============================================================================

/// Checks that a type has a specific kind.
///
/// Mirrors F* `check_kind_env : named_kind_env -> kind_ctx -> brrr_type -> kind -> bool`.
#[must_use]
pub fn check_kind(env: &NamedKindEnv, ctx: &KindCtx, ty: &BrrrType, expected: &Kind) -> bool {
    match infer_kind(env, ctx, ty) {
        Some(ref k) => k == expected,
        None => false,
    }
}

/// Checks that a type has kind `*` (is a proper type).
///
/// Mirrors F* `is_proper_type : kind_ctx -> brrr_type -> bool`.
///
/// Uses the default named kind environment.
#[must_use]
pub fn is_proper_type(ty: &BrrrType) -> bool {
    // Use an empty named kind environment for simpler checking.
    // Named types will fail to resolve, but primitive/numeric types will work.
    let empty_env = NamedKindEnv::new();
    let empty_ctx = KindCtx::new();
    check_kind(&empty_env, &empty_ctx, ty, &Kind::Star)
}

/// Checks that a type is a proper type, with explicit environments.
#[must_use]
pub fn is_proper_type_with_env(env: &NamedKindEnv, ctx: &KindCtx, ty: &BrrrType) -> bool {
    check_kind(env, ctx, ty, &Kind::Star)
}

/// Checks if a type is a type constructor (has kind `k -> ...`).
///
/// Returns `true` if the type has an arrow kind, `false` otherwise.
#[must_use]
pub fn is_type_constructor(ty: &BrrrType) -> bool {
    let empty_env = NamedKindEnv::new();
    let empty_ctx = KindCtx::new();
    matches!(infer_kind(&empty_env, &empty_ctx, ty), Some(Kind::Arrow(_, _)))
}

/// Checks if a type is a type constructor with explicit environments.
#[must_use]
pub fn is_type_constructor_with_env(env: &NamedKindEnv, ctx: &KindCtx, ty: &BrrrType) -> bool {
    matches!(infer_kind(env, ctx, ty), Some(Kind::Arrow(_, _)))
}

/// Infers the kind of a type using empty environments.
///
/// Convenience function for simple cases where named types and type variables
/// are not expected.
#[must_use]
pub fn kind_of_type(ty: &BrrrType) -> Option<Kind> {
    let empty_env = NamedKindEnv::new();
    let empty_ctx = KindCtx::new();
    infer_kind(&empty_env, &empty_ctx, ty)
}

/// Constructs an arrow kind of given arity: `* -> * -> ... -> *` (n arrows).
///
/// Mirrors F* `make_arrow_kind : nat -> kind`.
#[must_use]
pub fn make_arrow_kind(arity: usize) -> Kind {
    if arity == 0 {
        Kind::Star
    } else {
        Kind::arrow(Kind::Star, make_arrow_kind(arity - 1))
    }
}

// ============================================================================
// Free functions for F*-style compatibility
// ============================================================================

/// The kind of proper types `*`
///
/// Alias for `Kind::Star` matching F* `KStar`.
pub const STAR: Kind = Kind::Star;

/// The kind `* -> *` for unary type constructors
///
/// Returns the kind used by Option, Vec, Box, etc.
#[must_use]
pub fn arrow_1() -> Kind {
    Kind::type_to_type()
}

/// The kind `* -> * -> *` for binary type constructors
///
/// Returns the kind used by Result, Map, Either, etc.
#[must_use]
pub fn arrow_2() -> Kind {
    Kind::type2_to_type()
}

/// Check kind equality
///
/// Free function wrapper around `PartialEq` for F*-style usage.
#[must_use]
pub fn kind_eq(k1: &Kind, k2: &Kind) -> bool {
    k1 == k2
}

/// Get the arity of a kind (number of arrow arguments)
///
/// Free function wrapper around `Kind::arity()` for F*-style usage.
#[must_use]
pub fn kind_arity(k: &Kind) -> u32 {
    k.arity() as u32
}

/// Get the result kind after all applications
///
/// Free function wrapper around `Kind::result()` for F*-style usage.
#[must_use]
pub fn kind_result(k: &Kind) -> Kind {
    k.result().clone()
}

/// Check if a kind is `*` (proper type kind)
///
/// Free function wrapper around `Kind::is_type()` for F*-style usage.
#[must_use]
pub fn is_proper_kind(k: &Kind) -> bool {
    k.is_type()
}

#[cfg(test)]
mod tests {
    use super::*;
    use lasso::Rodeo;

    #[test]
    fn test_kind_constants() {
        assert!(Kind::TYPE.is_type());
        assert!(Kind::EFFECT.is_effect());
        assert!(Kind::LIFETIME.is_region());
    }

    #[test]
    fn test_kind_arity() {
        assert_eq!(Kind::Star.arity(), 0);
        assert_eq!(Kind::Row.arity(), 0);
        assert_eq!(Kind::Region.arity(), 0);
        assert_eq!(Kind::type_to_type().arity(), 1);
        assert_eq!(Kind::type2_to_type().arity(), 2);
        assert_eq!(Kind::type3_to_type().arity(), 3);
    }

    #[test]
    fn test_kind_result() {
        assert_eq!(*Kind::Star.result(), Kind::Star);
        assert_eq!(*Kind::type_to_type().result(), Kind::Star);
        assert_eq!(*Kind::type2_to_type().result(), Kind::Star);
        assert_eq!(*Kind::effect_to_type().result(), Kind::Star);
    }

    #[test]
    fn test_kind_apply() {
        let type_to_type = Kind::type_to_type();
        assert_eq!(type_to_type.apply(), Some(&Kind::Star));

        let type2 = Kind::type2_to_type();
        assert_eq!(type2.apply(), Some(&Kind::type_to_type()));

        assert_eq!(Kind::Star.apply(), None);
    }

    #[test]
    fn test_kind_apply_checked() {
        let type_to_type = Kind::type_to_type();
        assert_eq!(type_to_type.apply_checked(&Kind::Star), Some(&Kind::Star));
        assert_eq!(type_to_type.apply_checked(&Kind::Row), None);

        let effect_to_type = Kind::effect_to_type();
        assert_eq!(effect_to_type.apply_checked(&Kind::Row), Some(&Kind::Star));
        assert_eq!(effect_to_type.apply_checked(&Kind::Star), None);
    }

    #[test]
    fn test_kind_format() {
        assert_eq!(Kind::Star.format(), "*");
        assert_eq!(Kind::Row.format(), "Row");
        assert_eq!(Kind::Region.format(), "Region");
        assert_eq!(Kind::type_to_type().format(), "* -> *");
        assert_eq!(Kind::type2_to_type().format(), "* -> * -> *");
        assert_eq!(Kind::effect_to_type().format(), "Row -> *");

        // Test parenthesization for nested arrows on the left
        let nested = Kind::arrow(Kind::type_to_type(), Kind::Star);
        assert_eq!(nested.format(), "(* -> *) -> *");
    }

    #[test]
    fn test_kinded_var() {
        let mut rodeo = Rodeo::default();
        let alpha = rodeo.get_or_intern("alpha");

        let var = KindedVar::of_type(alpha);
        assert_eq!(var.kind, Kind::Star);

        let constructor = KindedVar::type_constructor(alpha);
        assert_eq!(constructor.kind, Kind::type_to_type());
    }

    #[test]
    fn test_kind_ctx() {
        let mut rodeo = Rodeo::default();
        let alpha = rodeo.get_or_intern("alpha");
        let beta = rodeo.get_or_intern("beta");

        let mut ctx = KindCtx::new();
        extend_kind_ctx(&mut ctx, alpha, Kind::Star);
        extend_kind_ctx(&mut ctx, beta, Kind::type_to_type());

        assert_eq!(lookup_kind(&alpha, &ctx), Some(&Kind::Star));
        assert_eq!(lookup_kind(&beta, &ctx), Some(&Kind::type_to_type()));
        assert_eq!(lookup_kind(&rodeo.get_or_intern("gamma"), &ctx), None);
    }

    #[test]
    fn test_kind_display() {
        assert_eq!(format!("{}", Kind::Star), "*");
        assert_eq!(format!("{}", Kind::type_to_type()), "* -> *");
    }

    #[test]
    fn test_kind_equality() {
        assert_eq!(Kind::Star, Kind::Star);
        assert_ne!(Kind::Star, Kind::Row);
        assert_eq!(Kind::type_to_type(), Kind::arrow(Kind::Star, Kind::Star));
    }

    #[test]
    fn test_kind_default() {
        assert_eq!(Kind::default(), Kind::Star);
    }

    #[test]
    fn test_star_constant() {
        assert_eq!(STAR, Kind::Star);
        assert!(is_proper_kind(&STAR));
    }

    #[test]
    fn test_arrow_constructors() {
        assert_eq!(arrow_1(), Kind::type_to_type());
        assert_eq!(arrow_2(), Kind::type2_to_type());
        assert_eq!(kind_arity(&arrow_1()), 1);
        assert_eq!(kind_arity(&arrow_2()), 2);
    }

    #[test]
    fn test_free_function_kind_eq() {
        assert!(kind_eq(&Kind::Star, &Kind::Star));
        assert!(kind_eq(&Kind::Row, &Kind::Row));
        assert!(!kind_eq(&Kind::Star, &Kind::Row));
        assert!(kind_eq(&arrow_1(), &Kind::type_to_type()));
    }

    #[test]
    fn test_free_function_kind_arity() {
        assert_eq!(kind_arity(&Kind::Star), 0);
        assert_eq!(kind_arity(&Kind::Row), 0);
        assert_eq!(kind_arity(&Kind::Region), 0);
        assert_eq!(kind_arity(&arrow_1()), 1);
        assert_eq!(kind_arity(&arrow_2()), 2);
    }

    #[test]
    fn test_free_function_kind_result() {
        assert_eq!(kind_result(&Kind::Star), Kind::Star);
        assert_eq!(kind_result(&arrow_1()), Kind::Star);
        assert_eq!(kind_result(&arrow_2()), Kind::Star);
        assert_eq!(kind_result(&Kind::effect_to_type()), Kind::Star);
    }

    #[test]
    fn test_free_function_is_proper_kind() {
        assert!(is_proper_kind(&Kind::Star));
        assert!(is_proper_kind(&STAR));
        assert!(!is_proper_kind(&Kind::Row));
        assert!(!is_proper_kind(&Kind::Region));
        assert!(!is_proper_kind(&arrow_1()));
    }

    // ========================================================================
    // Tests for Kind Inference
    // ========================================================================

    #[test]
    fn test_default_kind_env_entries() {
        let entries = default_kind_env_entries();
        // Check some key entries exist
        let names: Vec<&str> = entries.iter().map(|(n, _)| *n).collect();
        assert!(names.contains(&"Option"));
        assert!(names.contains(&"Vec"));
        assert!(names.contains(&"Result"));
        assert!(names.contains(&"Functor"));
        assert!(names.contains(&"IO"));
        assert!(names.contains(&"Static"));
    }

    #[test]
    fn test_default_kind_env_kinds() {
        let entries = default_kind_env_entries();
        let entry_map: std::collections::HashMap<&str, Kind> = entries.into_iter().collect();

        // Option : * -> *
        assert_eq!(entry_map.get("Option"), Some(&Kind::type_to_type()));

        // Result : * -> * -> *
        assert_eq!(entry_map.get("Result"), Some(&Kind::type2_to_type()));

        // Functor : (* -> *) -> *
        assert_eq!(
            entry_map.get("Functor"),
            Some(&Kind::arrow(Kind::type_to_type(), Kind::Star))
        );

        // IO : Row
        assert_eq!(entry_map.get("IO"), Some(&Kind::Row));

        // Static : Region
        assert_eq!(entry_map.get("Static"), Some(&Kind::Region));
    }

    #[test]
    fn test_infer_kind_primitives() {
        use super::super::PrimKind;
        let env = NamedKindEnv::new();
        let ctx = KindCtx::new();

        // All primitives have kind *
        assert_eq!(
            infer_kind(&env, &ctx, &BrrrType::Prim(PrimKind::Unit)),
            Some(Kind::Star)
        );
        assert_eq!(
            infer_kind(&env, &ctx, &BrrrType::Prim(PrimKind::Bool)),
            Some(Kind::Star)
        );
        assert_eq!(
            infer_kind(&env, &ctx, &BrrrType::Prim(PrimKind::String)),
            Some(Kind::Star)
        );
        assert_eq!(
            infer_kind(&env, &ctx, &BrrrType::Prim(PrimKind::Never)),
            Some(Kind::Star)
        );
    }

    #[test]
    fn test_infer_kind_numerics() {
        use super::super::{IntType, NumericType};
        let env = NamedKindEnv::new();
        let ctx = KindCtx::new();

        // All numeric types have kind *
        assert_eq!(
            infer_kind(&env, &ctx, &BrrrType::Numeric(NumericType::Int(IntType::I32))),
            Some(Kind::Star)
        );
        assert_eq!(
            infer_kind(&env, &ctx, &BrrrType::Numeric(NumericType::Int(IntType::U64))),
            Some(Kind::Star)
        );
    }

    #[test]
    fn test_infer_kind_wrappers() {
        use super::super::WrapperKind;
        let env = NamedKindEnv::new();
        let ctx = KindCtx::new();

        // Wrapper with * inner has kind *
        let option_int = BrrrType::Wrap(WrapperKind::Option, Box::new(BrrrType::BOOL));
        assert_eq!(infer_kind(&env, &ctx, &option_int), Some(Kind::Star));

        // Nested wrappers still have kind *
        let box_option_int =
            BrrrType::Wrap(WrapperKind::Box, Box::new(option_int.clone()));
        assert_eq!(infer_kind(&env, &ctx, &box_option_int), Some(Kind::Star));
    }

    #[test]
    fn test_infer_kind_tuples() {
        let env = NamedKindEnv::new();
        let ctx = KindCtx::new();

        // Empty tuple has kind *
        assert_eq!(infer_kind(&env, &ctx, &BrrrType::Tuple(vec![])), Some(Kind::Star));

        // Tuple of * types has kind *
        let tuple = BrrrType::Tuple(vec![BrrrType::BOOL, BrrrType::STRING, BrrrType::UNIT]);
        assert_eq!(infer_kind(&env, &ctx, &tuple), Some(Kind::Star));
    }

    #[test]
    fn test_infer_kind_result() {
        let env = NamedKindEnv::new();
        let ctx = KindCtx::new();

        // Result with * types has kind *
        let result = BrrrType::Result(Box::new(BrrrType::BOOL), Box::new(BrrrType::STRING));
        assert_eq!(infer_kind(&env, &ctx, &result), Some(Kind::Star));
    }

    #[test]
    fn test_infer_kind_type_var() {
        let env = NamedKindEnv::new();
        let mut rodeo = Rodeo::default();
        let alpha = rodeo.get_or_intern("alpha");
        let beta = rodeo.get_or_intern("beta");

        // Type var not in context returns None
        let empty_ctx = KindCtx::new();
        assert_eq!(infer_kind(&env, &empty_ctx, &BrrrType::Var(alpha)), None);

        // Type var in context returns its kind
        let mut ctx = KindCtx::new();
        extend_kind_ctx(&mut ctx, alpha, Kind::Star);
        extend_kind_ctx(&mut ctx, beta, Kind::type_to_type());

        assert_eq!(
            infer_kind(&env, &ctx, &BrrrType::Var(alpha)),
            Some(Kind::Star)
        );
        assert_eq!(
            infer_kind(&env, &ctx, &BrrrType::Var(beta)),
            Some(Kind::type_to_type())
        );
    }

    #[test]
    fn test_infer_kind_named() {
        let mut rodeo = Rodeo::default();
        let env = default_kind_env(|s| rodeo.get_or_intern(s));
        let ctx = KindCtx::new();

        // Named types lookup in environment
        let option_name = rodeo.get_or_intern("Option");
        let result_name = rodeo.get_or_intern("Result");
        let functor_name = rodeo.get_or_intern("Functor");

        assert_eq!(
            infer_kind(&env, &ctx, &BrrrType::Named(option_name)),
            Some(Kind::type_to_type())
        );
        assert_eq!(
            infer_kind(&env, &ctx, &BrrrType::Named(result_name)),
            Some(Kind::type2_to_type())
        );
        assert_eq!(
            infer_kind(&env, &ctx, &BrrrType::Named(functor_name)),
            Some(Kind::arrow(Kind::type_to_type(), Kind::Star))
        );

        // Unknown named type returns None
        let unknown = rodeo.get_or_intern("UnknownType");
        assert_eq!(infer_kind(&env, &ctx, &BrrrType::Named(unknown)), None);
    }

    #[test]
    fn test_infer_kind_type_application() {
        let mut rodeo = Rodeo::default();
        let env = default_kind_env(|s| rodeo.get_or_intern(s));
        let ctx = KindCtx::new();

        let option_name = rodeo.get_or_intern("Option");
        let result_name = rodeo.get_or_intern("Result");

        // Option<Int> : * (applying * -> * to *)
        let option_int = BrrrType::App(
            Box::new(BrrrType::Named(option_name)),
            vec![BrrrType::BOOL],
        );
        assert_eq!(infer_kind(&env, &ctx, &option_int), Some(Kind::Star));

        // Result<Int, String> : * (applying * -> * -> * to two *)
        let result_type = BrrrType::App(
            Box::new(BrrrType::Named(result_name)),
            vec![BrrrType::BOOL, BrrrType::STRING],
        );
        assert_eq!(infer_kind(&env, &ctx, &result_type), Some(Kind::Star));

        // Partial application: Result<Int> : * -> *
        let partial_result = BrrrType::App(
            Box::new(BrrrType::Named(result_name)),
            vec![BrrrType::BOOL],
        );
        assert_eq!(
            infer_kind(&env, &ctx, &partial_result),
            Some(Kind::type_to_type())
        );
    }

    #[test]
    fn test_check_kind() {
        let env = NamedKindEnv::new();
        let ctx = KindCtx::new();

        assert!(check_kind(&env, &ctx, &BrrrType::BOOL, &Kind::Star));
        assert!(!check_kind(&env, &ctx, &BrrrType::BOOL, &Kind::Row));
        assert!(!check_kind(&env, &ctx, &BrrrType::BOOL, &Kind::type_to_type()));
    }

    #[test]
    fn test_is_proper_type() {
        // Primitives are proper types
        assert!(is_proper_type(&BrrrType::BOOL));
        assert!(is_proper_type(&BrrrType::STRING));
        assert!(is_proper_type(&BrrrType::UNIT));

        // Tuples of proper types are proper types
        assert!(is_proper_type(&BrrrType::Tuple(vec![BrrrType::BOOL])));
    }

    #[test]
    fn test_is_type_constructor() {
        // Named types that are type constructors
        let mut rodeo = Rodeo::default();
        let env = default_kind_env(|s| rodeo.get_or_intern(s));
        let ctx = KindCtx::new();

        let option_name = rodeo.get_or_intern("Option");
        let option_ty = BrrrType::Named(option_name);
        assert!(is_type_constructor_with_env(&env, &ctx, &option_ty));

        // Primitives are not type constructors
        assert!(!is_type_constructor(&BrrrType::BOOL));
    }

    #[test]
    fn test_kind_of_type() {
        // Simple types
        assert_eq!(kind_of_type(&BrrrType::BOOL), Some(Kind::Star));
        assert_eq!(kind_of_type(&BrrrType::UNIT), Some(Kind::Star));

        // Tuples
        assert_eq!(
            kind_of_type(&BrrrType::Tuple(vec![BrrrType::BOOL, BrrrType::STRING])),
            Some(Kind::Star)
        );
    }

    #[test]
    fn test_make_arrow_kind() {
        assert_eq!(make_arrow_kind(0), Kind::Star);
        assert_eq!(make_arrow_kind(1), Kind::type_to_type());
        assert_eq!(make_arrow_kind(2), Kind::type2_to_type());
        assert_eq!(make_arrow_kind(3), Kind::type3_to_type());
    }

    #[test]
    fn test_struct_kind_fallback() {
        use super::super::{FieldType, StructType, Visibility};
        let env = NamedKindEnv::new();
        let ctx = KindCtx::new();
        let mut rodeo = Rodeo::default();

        let point_name = rodeo.get_or_intern("Point");
        let x_name = rodeo.get_or_intern("x");

        let point_struct = StructType::new(
            point_name,
            vec![FieldType {
                name: x_name,
                ty: BrrrType::BOOL,
                vis: Visibility::Public,
            }],
        );

        // Unregistered struct falls back to kind *
        let struct_ty = BrrrType::Struct(point_struct);
        assert_eq!(infer_kind(&env, &ctx, &struct_ty), Some(Kind::Star));
    }

    #[test]
    fn test_enum_kind_fallback() {
        use super::super::{EnumType, VariantType};
        let env = NamedKindEnv::new();
        let ctx = KindCtx::new();
        let mut rodeo = Rodeo::default();

        let option_name = rodeo.get_or_intern("MyOption");
        let none_name = rodeo.get_or_intern("None");
        let some_name = rodeo.get_or_intern("Some");

        let option_enum = EnumType::new(
            option_name,
            vec![
                VariantType::unit(none_name),
                VariantType::newtype(some_name, BrrrType::BOOL),
            ],
        );

        // Unregistered enum falls back to kind *
        let enum_ty = BrrrType::Enum(option_enum);
        assert_eq!(infer_kind(&env, &ctx, &enum_ty), Some(Kind::Star));
    }

    #[test]
    fn test_function_type_kind() {
        use super::super::{FuncType, ParamType};
        let env = NamedKindEnv::new();
        let ctx = KindCtx::new();

        // Function with * param and * return has kind *
        let func = FuncType::pure(
            vec![ParamType::unnamed(BrrrType::BOOL)],
            BrrrType::STRING,
        );
        let func_ty = BrrrType::Func(Box::new(func));
        assert_eq!(infer_kind(&env, &ctx, &func_ty), Some(Kind::Star));
    }
}
