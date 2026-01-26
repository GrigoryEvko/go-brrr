//! Variance system for type constructors
//!
//! Mirrors F* Kinds.fst lines 802-1000:
//! ```fstar
//! type variance =
//!   | VCovariant     (* + position: T <: U implies F T <: F U *)
//!   | VContravariant (* - position: T <: U implies F U <: F T *)
//!   | VInvariant     (* = position: must be equal *)
//!   | VBivariant     (* * position: ignored, always compatible *)
//! ```

use std::collections::HashMap;

use super::{BrrrType, TypeName, TypeVar, Variance, WrapperKind};

/// Variance environment - maps type names to the variance of each type parameter.
///
/// For example: `Result` has variances `[Covariant, Covariant]` because both
/// `T` and `E` in `Result<T, E>` are covariant.
///
/// Mirrors F* `type variance_env = list (type_name & list variance)`.
pub type VarianceEnv = HashMap<TypeName, Vec<Variance>>;

/// Combine two variances when composing type constructors.
///
/// This follows the F* specification exactly:
/// - Bivariant absorbs everything (unused position)
/// - Invariant absorbs next (no subtyping possible)
/// - Covariant + Covariant = Covariant
/// - Contravariant + Contravariant = Covariant (double negation)
/// - Covariant + Contravariant = Contravariant
/// - Contravariant + Covariant = Contravariant
///
/// Mirrors F* `combine_variance`:
/// ```fstar
/// let combine_variance (v1 v2: variance) : variance =
///   match v1, v2 with
///   | VBivariant, _ | _, VBivariant -> VBivariant
///   | VInvariant, _ | _, VInvariant -> VInvariant
///   | VCovariant, VCovariant -> VCovariant
///   | VContravariant, VContravariant -> VCovariant
///   | VCovariant, VContravariant -> VContravariant
///   | VContravariant, VCovariant -> VContravariant
/// ```
#[must_use]
pub const fn combine_variance(v1: Variance, v2: Variance) -> Variance {
    match (v1, v2) {
        // Bivariant absorbs everything - position is completely unused
        (Variance::Bivariant, _) | (_, Variance::Bivariant) => Variance::Bivariant,

        // Invariant absorbs next - must be exactly equal
        (Variance::Invariant, _) | (_, Variance::Invariant) => Variance::Invariant,

        // Same variance preserves direction
        (Variance::Covariant, Variance::Covariant) => Variance::Covariant,

        // Double negation: contra + contra = covariant
        (Variance::Contravariant, Variance::Contravariant) => Variance::Covariant,

        // Mixed: one negation = contravariant
        (Variance::Covariant, Variance::Contravariant)
        | (Variance::Contravariant, Variance::Covariant) => Variance::Contravariant,
    }
}

/// Negate variance (for contravariant positions like function parameters).
///
/// - Covariant becomes Contravariant
/// - Contravariant becomes Covariant
/// - Invariant stays Invariant
/// - Bivariant stays Bivariant
///
/// Mirrors F* `negate_variance`:
/// ```fstar
/// let negate_variance (v: variance) : variance =
///   match v with
///   | VCovariant -> VContravariant
///   | VContravariant -> VCovariant
///   | VInvariant -> VInvariant
///   | VBivariant -> VBivariant
/// ```
#[must_use]
pub const fn negate_variance(v: Variance) -> Variance {
    v.negate()
}

/// Creates the default variance environment with standard type constructors.
///
/// Standard variances:
/// - `Option<T>`: `[+]` (covariant)
/// - `Vec<T>`: `[+]` (covariant)
/// - `Box<T>`: `[+]` (covariant)
/// - `Rc<T>`: `[+]` (covariant)
/// - `Arc<T>`: `[+]` (covariant)
/// - `Result<T, E>`: `[+, +]` (both covariant)
/// - `Map<K, V>`: `[+, +]` (both covariant for immutable)
/// - `Ref<T>`: `[+]` (covariant - shared reference)
/// - `RefMut<T>`: `[=]` (invariant - mutable reference)
/// - `Cell<T>`: `[=]` (invariant - interior mutability)
/// - `RefCell<T>`: `[=]` (invariant - interior mutability)
/// - `Mutex<T>`: `[=]` (invariant - interior mutability)
/// - `RwLock<T>`: `[=]` (invariant - interior mutability)
/// - `Raw<T>`: `[=]` (invariant - raw pointer for safety)
/// - `Fn<A, R>`: `[-, +]` (contravariant in args, covariant in return)
///
/// # Arguments
/// * `intern` - A closure that interns a string and returns a `TypeName` (Spur)
#[must_use]
pub fn default_variance_env<F>(mut intern: F) -> VarianceEnv
where
    F: FnMut(&str) -> TypeName,
{
    let mut env = HashMap::new();

    // Covariant type constructors (+ position)
    for name in [
        "Option", "Vec", "List", "Set", "Box", "Rc", "Arc", "Ref", "Future", "Promise", "Iterator",
        "Stream",
    ] {
        env.insert(intern(name), vec![Variance::Covariant]);
    }

    // Invariant type constructors (= position) - mutable or interior mutability
    for name in ["RefMut", "Cell", "RefCell", "Mutex", "RwLock", "Raw"] {
        env.insert(intern(name), vec![Variance::Invariant]);
    }

    // Binary covariant type constructors
    for name in ["Result", "Either", "Pair"] {
        env.insert(intern(name), vec![Variance::Covariant, Variance::Covariant]);
    }

    // Map types: covariant in both key and value for immutable maps
    for name in ["Map", "HashMap", "BTreeMap"] {
        env.insert(intern(name), vec![Variance::Covariant, Variance::Covariant]);
    }

    // Function types: contravariant in input, covariant in output
    // Fn1<A, R> = A -> R
    env.insert(
        intern("Fn1"),
        vec![Variance::Contravariant, Variance::Covariant],
    );

    // Fn2<A, B, R> = (A, B) -> R
    env.insert(
        intern("Fn2"),
        vec![
            Variance::Contravariant,
            Variance::Contravariant,
            Variance::Covariant,
        ],
    );

    // Fn3<A, B, C, R> = (A, B, C) -> R
    env.insert(
        intern("Fn3"),
        vec![
            Variance::Contravariant,
            Variance::Contravariant,
            Variance::Contravariant,
            Variance::Covariant,
        ],
    );

    env
}

/// Compute the variance of a type variable within a type.
///
/// This recursively walks the type structure, tracking variance changes
/// through contravariant positions (like function parameters).
///
/// Returns `Bivariant` if the variable doesn't appear in the type (unused).
///
/// # Arguments
/// * `ty` - The type to analyze
/// * `x` - The type variable to find
/// * `env` - The variance environment for named types
///
/// # Examples
/// - `variance_of(T, T)` = Covariant
/// - `variance_of(Option<T>, T)` = Covariant
/// - `variance_of((A) -> T, T)` = Covariant (return position)
/// - `variance_of((T) -> A, T)` = Contravariant (parameter position)
/// - `variance_of(&mut T, T)` = Invariant
///
/// Mirrors F* `variance_of : variance_env -> brrr_type -> type_var -> variance`.
#[must_use]
pub fn variance_of(ty: &BrrrType, x: TypeVar, env: &VarianceEnv) -> Variance {
    variance_of_inner(ty, x, env, Variance::Covariant)
}

/// Internal recursive helper that tracks current variance context.
fn variance_of_inner(
    ty: &BrrrType,
    x: TypeVar,
    env: &VarianceEnv,
    current: Variance,
) -> Variance {
    match ty {
        // Type variable: if it's the one we're looking for, return current variance
        BrrrType::Var(v) => {
            if *v == x {
                current
            } else {
                Variance::Bivariant // Not present, unused position
            }
        }

        // Primitives and numerics don't contain type variables
        BrrrType::Prim(_) | BrrrType::Numeric(_) | BrrrType::Named(_) => Variance::Bivariant,

        // Wrapper types: variance depends on wrapper kind
        BrrrType::Wrap(kind, inner) => {
            let wrapper_variance = wrapper_kind_variance(*kind);
            let combined = combine_variance(current, wrapper_variance);
            variance_of_inner(inner, x, env, combined)
        }

        // Sized arrays: covariant in element type
        BrrrType::SizedArray(_, inner) => variance_of_inner(inner, x, env, current),

        // Modal types: covariant
        BrrrType::Modal(_, inner) => variance_of_inner(inner, x, env, current),

        // Result: both positions are covariant
        BrrrType::Result(ok, err) => {
            let v_ok = variance_of_inner(ok, x, env, current);
            let v_err = variance_of_inner(err, x, env, current);
            join_variances(v_ok, v_err)
        }

        // Tuple: all positions are covariant
        BrrrType::Tuple(elems) => {
            let mut result = Variance::Bivariant;
            for elem in elems {
                let v = variance_of_inner(elem, x, env, current);
                result = join_variances(result, v);
            }
            result
        }

        // Function type: parameters are contravariant, return is covariant
        BrrrType::Func(func) => {
            let mut result = Variance::Bivariant;

            // Parameters are in contravariant position
            let param_variance = combine_variance(current, Variance::Contravariant);
            for param in &func.params {
                let v = variance_of_inner(&param.ty, x, env, param_variance);
                result = join_variances(result, v);
            }

            // Return type is in covariant position (relative to current)
            let ret_v = variance_of_inner(&func.return_type, x, env, current);
            join_variances(result, ret_v)
        }

        // Type application: lookup constructor variance and apply to args
        BrrrType::App(constructor, args) => {
            // First check if variable is in the constructor itself
            let mut result = variance_of_inner(constructor, x, env, current);

            // Then check each argument with its corresponding variance
            if let BrrrType::Named(name) = constructor.as_ref() {
                if let Some(variances) = env.get(name) {
                    for (arg, &arg_variance) in args.iter().zip(variances.iter()) {
                        let combined = combine_variance(current, arg_variance);
                        let v = variance_of_inner(arg, x, env, combined);
                        result = join_variances(result, v);
                    }
                } else {
                    // Unknown constructor: assume covariant for safety
                    for arg in args {
                        let v = variance_of_inner(arg, x, env, current);
                        result = join_variances(result, v);
                    }
                }
            } else {
                // Non-named constructor: check args with current variance
                for arg in args {
                    let v = variance_of_inner(arg, x, env, current);
                    result = join_variances(result, v);
                }
            }

            result
        }

        // Struct: all field types are covariant
        BrrrType::Struct(s) => {
            let mut result = Variance::Bivariant;
            for field in &s.fields {
                let v = variance_of_inner(&field.ty, x, env, current);
                result = join_variances(result, v);
            }
            result
        }

        // Enum: all variant fields are covariant
        BrrrType::Enum(e) => {
            let mut result = Variance::Bivariant;
            for variant in &e.variants {
                for field in &variant.fields {
                    let v = variance_of_inner(field, x, env, current);
                    result = join_variances(result, v);
                }
            }
            result
        }

        // Interface: method parameters are contravariant, return types covariant
        BrrrType::Interface(iface) => {
            let mut result = Variance::Bivariant;
            for method in &iface.methods {
                // Parameters are in contravariant position
                let param_variance = combine_variance(current, Variance::Contravariant);
                for param in &method.params {
                    let v = variance_of_inner(&param.ty, x, env, param_variance);
                    result = join_variances(result, v);
                }
                // Return type is covariant
                let ret_v = variance_of_inner(&method.return_type, x, env, current);
                result = join_variances(result, ret_v);
            }
            result
        }
    }
}

/// Get the variance of a wrapper kind.
fn wrapper_kind_variance(kind: WrapperKind) -> Variance {
    match kind {
        // Covariant wrappers
        WrapperKind::Array
        | WrapperKind::Slice
        | WrapperKind::Option
        | WrapperKind::Box
        | WrapperKind::Ref
        | WrapperKind::Rc
        | WrapperKind::Arc => Variance::Covariant,

        // Invariant wrappers (mutable access)
        WrapperKind::RefMut | WrapperKind::Raw => Variance::Invariant,
    }
}

/// Join two variances when a variable appears in multiple positions.
///
/// This computes the "meet" in the variance lattice:
/// - If variable appears in both covariant and contravariant positions -> Invariant
/// - If variable appears only in covariant positions -> Covariant
/// - If variable appears only in contravariant positions -> Contravariant
/// - If variable doesn't appear (Bivariant) in one branch, take the other
fn join_variances(v1: Variance, v2: Variance) -> Variance {
    match (v1, v2) {
        // Bivariant means "not present", so take the other
        (Variance::Bivariant, v) | (v, Variance::Bivariant) => v,

        // Same variance: keep it
        (Variance::Covariant, Variance::Covariant) => Variance::Covariant,
        (Variance::Contravariant, Variance::Contravariant) => Variance::Contravariant,
        (Variance::Invariant, Variance::Invariant) => Variance::Invariant,

        // Mixed covariant/contravariant -> invariant
        (Variance::Covariant, Variance::Contravariant)
        | (Variance::Contravariant, Variance::Covariant) => Variance::Invariant,

        // Invariant absorbs everything else
        (Variance::Invariant, _) | (_, Variance::Invariant) => Variance::Invariant,
    }
}

/// Get the variance of a specific type parameter by index.
///
/// For a type like `Result<T, E>`, `variance_of_param(..., 0)` returns
/// the variance of the first type parameter (T).
///
/// # Arguments
/// * `type_name` - The name of the type constructor
/// * `param_idx` - The 0-based index of the type parameter
/// * `env` - The variance environment
///
/// Returns `None` if the type is not in the environment or the index is out of bounds.
#[must_use]
pub fn variance_of_param(type_name: TypeName, param_idx: usize, env: &VarianceEnv) -> Option<Variance> {
    env.get(&type_name)
        .and_then(|variances| variances.get(param_idx).copied())
}

#[cfg(test)]
mod tests {
    use super::*;
    use lasso::Rodeo;

    #[test]
    fn test_combine_variance_bivariant_absorbs() {
        // Bivariant absorbs everything (F* semantics)
        assert_eq!(
            combine_variance(Variance::Bivariant, Variance::Covariant),
            Variance::Bivariant
        );
        assert_eq!(
            combine_variance(Variance::Bivariant, Variance::Contravariant),
            Variance::Bivariant
        );
        assert_eq!(
            combine_variance(Variance::Bivariant, Variance::Invariant),
            Variance::Bivariant
        );
        assert_eq!(
            combine_variance(Variance::Covariant, Variance::Bivariant),
            Variance::Bivariant
        );
        assert_eq!(
            combine_variance(Variance::Invariant, Variance::Bivariant),
            Variance::Bivariant
        );
    }

    #[test]
    fn test_combine_variance_invariant_absorbs_after_bivariant() {
        // Invariant absorbs when no Bivariant present
        assert_eq!(
            combine_variance(Variance::Invariant, Variance::Covariant),
            Variance::Invariant
        );
        assert_eq!(
            combine_variance(Variance::Invariant, Variance::Contravariant),
            Variance::Invariant
        );
        assert_eq!(
            combine_variance(Variance::Covariant, Variance::Invariant),
            Variance::Invariant
        );
        assert_eq!(
            combine_variance(Variance::Contravariant, Variance::Invariant),
            Variance::Invariant
        );
    }

    #[test]
    fn test_combine_variance_covariant_covariant() {
        assert_eq!(
            combine_variance(Variance::Covariant, Variance::Covariant),
            Variance::Covariant
        );
    }

    #[test]
    fn test_combine_variance_double_negation() {
        // Contra + Contra = Covariant (double negation)
        assert_eq!(
            combine_variance(Variance::Contravariant, Variance::Contravariant),
            Variance::Covariant
        );
    }

    #[test]
    fn test_combine_variance_mixed() {
        // Mixed gives Contravariant
        assert_eq!(
            combine_variance(Variance::Covariant, Variance::Contravariant),
            Variance::Contravariant
        );
        assert_eq!(
            combine_variance(Variance::Contravariant, Variance::Covariant),
            Variance::Contravariant
        );
    }

    #[test]
    fn test_negate_variance() {
        assert_eq!(negate_variance(Variance::Covariant), Variance::Contravariant);
        assert_eq!(negate_variance(Variance::Contravariant), Variance::Covariant);
        assert_eq!(negate_variance(Variance::Invariant), Variance::Invariant);
        assert_eq!(negate_variance(Variance::Bivariant), Variance::Bivariant);
    }

    #[test]
    fn test_default_variance_env() {
        let mut rodeo = Rodeo::default();
        let env = default_variance_env(|s| rodeo.get_or_intern(s));

        // Check covariant types
        let option = rodeo.get_or_intern("Option");
        assert_eq!(env.get(&option), Some(&vec![Variance::Covariant]));

        let vec = rodeo.get_or_intern("Vec");
        assert_eq!(env.get(&vec), Some(&vec![Variance::Covariant]));

        // Check invariant types
        let ref_mut = rodeo.get_or_intern("RefMut");
        assert_eq!(env.get(&ref_mut), Some(&vec![Variance::Invariant]));

        let cell = rodeo.get_or_intern("Cell");
        assert_eq!(env.get(&cell), Some(&vec![Variance::Invariant]));

        // Check binary types
        let result = rodeo.get_or_intern("Result");
        assert_eq!(
            env.get(&result),
            Some(&vec![Variance::Covariant, Variance::Covariant])
        );

        // Check function types
        let fn1 = rodeo.get_or_intern("Fn1");
        assert_eq!(
            env.get(&fn1),
            Some(&vec![Variance::Contravariant, Variance::Covariant])
        );
    }

    #[test]
    fn test_variance_of_type_var() {
        let mut rodeo = Rodeo::default();
        let env = default_variance_env(|s| rodeo.get_or_intern(s));
        let t = rodeo.get_or_intern("T");
        let u = rodeo.get_or_intern("U");

        // Variable itself is covariant
        let ty = BrrrType::Var(t);
        assert_eq!(variance_of(&ty, t, &env), Variance::Covariant);

        // Different variable is bivariant (not present)
        assert_eq!(variance_of(&ty, u, &env), Variance::Bivariant);
    }

    #[test]
    fn test_variance_of_wrapper() {
        let mut rodeo = Rodeo::default();
        let env = default_variance_env(|s| rodeo.get_or_intern(s));
        let t = rodeo.get_or_intern("T");

        // Option<T>: T is covariant
        let option_t = BrrrType::Wrap(WrapperKind::Option, Box::new(BrrrType::Var(t)));
        assert_eq!(variance_of(&option_t, t, &env), Variance::Covariant);

        // &mut T: T is invariant
        let ref_mut_t = BrrrType::Wrap(WrapperKind::RefMut, Box::new(BrrrType::Var(t)));
        assert_eq!(variance_of(&ref_mut_t, t, &env), Variance::Invariant);
    }

    #[test]
    fn test_variance_of_function() {
        use super::super::{FuncType, ParamType};

        let mut rodeo = Rodeo::default();
        let env = default_variance_env(|s| rodeo.get_or_intern(s));
        let t = rodeo.get_or_intern("T");
        let u = rodeo.get_or_intern("U");

        // fn(T) -> U: T is contravariant, U is covariant
        let func = FuncType::pure(
            vec![ParamType::unnamed(BrrrType::Var(t))],
            BrrrType::Var(u),
        );
        let func_ty = BrrrType::Func(Box::new(func));

        assert_eq!(variance_of(&func_ty, t, &env), Variance::Contravariant);
        assert_eq!(variance_of(&func_ty, u, &env), Variance::Covariant);
    }

    #[test]
    fn test_variance_of_function_same_var() {
        use super::super::{FuncType, ParamType};

        let mut rodeo = Rodeo::default();
        let env = default_variance_env(|s| rodeo.get_or_intern(s));
        let t = rodeo.get_or_intern("T");

        // fn(T) -> T: T appears in both positions -> invariant
        let func = FuncType::pure(
            vec![ParamType::unnamed(BrrrType::Var(t))],
            BrrrType::Var(t),
        );
        let func_ty = BrrrType::Func(Box::new(func));

        assert_eq!(variance_of(&func_ty, t, &env), Variance::Invariant);
    }

    #[test]
    fn test_variance_of_result() {
        let mut rodeo = Rodeo::default();
        let env = default_variance_env(|s| rodeo.get_or_intern(s));
        let t = rodeo.get_or_intern("T");
        let e = rodeo.get_or_intern("E");

        // Result<T, E>: both are covariant
        let result_ty = BrrrType::Result(
            Box::new(BrrrType::Var(t)),
            Box::new(BrrrType::Var(e)),
        );

        assert_eq!(variance_of(&result_ty, t, &env), Variance::Covariant);
        assert_eq!(variance_of(&result_ty, e, &env), Variance::Covariant);
    }

    #[test]
    fn test_variance_of_tuple() {
        let mut rodeo = Rodeo::default();
        let env = default_variance_env(|s| rodeo.get_or_intern(s));
        let t = rodeo.get_or_intern("T");
        let u = rodeo.get_or_intern("U");

        // (T, U): both are covariant
        let tuple_ty = BrrrType::Tuple(vec![BrrrType::Var(t), BrrrType::Var(u)]);

        assert_eq!(variance_of(&tuple_ty, t, &env), Variance::Covariant);
        assert_eq!(variance_of(&tuple_ty, u, &env), Variance::Covariant);
    }

    #[test]
    fn test_variance_of_param() {
        let mut rodeo = Rodeo::default();
        let env = default_variance_env(|s| rodeo.get_or_intern(s));

        let result = rodeo.get_or_intern("Result");
        assert_eq!(variance_of_param(result, 0, &env), Some(Variance::Covariant));
        assert_eq!(variance_of_param(result, 1, &env), Some(Variance::Covariant));
        assert_eq!(variance_of_param(result, 2, &env), None); // Out of bounds

        let fn1 = rodeo.get_or_intern("Fn1");
        assert_eq!(variance_of_param(fn1, 0, &env), Some(Variance::Contravariant));
        assert_eq!(variance_of_param(fn1, 1, &env), Some(Variance::Covariant));

        let unknown = rodeo.get_or_intern("Unknown");
        assert_eq!(variance_of_param(unknown, 0, &env), None); // Not in env
    }

    #[test]
    fn test_join_variances() {
        // Bivariant with anything takes the other
        assert_eq!(join_variances(Variance::Bivariant, Variance::Covariant), Variance::Covariant);
        assert_eq!(join_variances(Variance::Covariant, Variance::Bivariant), Variance::Covariant);

        // Same variance stays same
        assert_eq!(join_variances(Variance::Covariant, Variance::Covariant), Variance::Covariant);
        assert_eq!(join_variances(Variance::Contravariant, Variance::Contravariant), Variance::Contravariant);

        // Mixed becomes invariant
        assert_eq!(join_variances(Variance::Covariant, Variance::Contravariant), Variance::Invariant);
        assert_eq!(join_variances(Variance::Contravariant, Variance::Covariant), Variance::Invariant);

        // Invariant absorbs
        assert_eq!(join_variances(Variance::Invariant, Variance::Covariant), Variance::Invariant);
        assert_eq!(join_variances(Variance::Covariant, Variance::Invariant), Variance::Invariant);
    }

    #[test]
    fn test_wrapper_kind_variance() {
        // Covariant wrappers
        assert_eq!(wrapper_kind_variance(WrapperKind::Option), Variance::Covariant);
        assert_eq!(wrapper_kind_variance(WrapperKind::Box), Variance::Covariant);
        assert_eq!(wrapper_kind_variance(WrapperKind::Ref), Variance::Covariant);

        // Invariant wrappers
        assert_eq!(wrapper_kind_variance(WrapperKind::RefMut), Variance::Invariant);
        assert_eq!(wrapper_kind_variance(WrapperKind::Raw), Variance::Invariant);
    }

    #[test]
    fn test_nested_variance() {
        let mut rodeo = Rodeo::default();
        let env = default_variance_env(|s| rodeo.get_or_intern(s));
        let t = rodeo.get_or_intern("T");

        // Option<Option<T>>: T is still covariant
        let inner = BrrrType::Wrap(WrapperKind::Option, Box::new(BrrrType::Var(t)));
        let outer = BrrrType::Wrap(WrapperKind::Option, Box::new(inner));
        assert_eq!(variance_of(&outer, t, &env), Variance::Covariant);

        // &mut Option<T>: T is invariant (invariant propagates)
        let opt_t = BrrrType::Wrap(WrapperKind::Option, Box::new(BrrrType::Var(t)));
        let ref_mut_opt = BrrrType::Wrap(WrapperKind::RefMut, Box::new(opt_t));
        assert_eq!(variance_of(&ref_mut_opt, t, &env), Variance::Invariant);
    }
}
