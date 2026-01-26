//! Core type definitions mirroring F* BrrrTypes.fsti
//!
//! 12 type constructors for SMT tractability (matching brrr-lang specification).
//!
//! # Kind System
//! Types are classified by kinds:
//! - `*` (Star) - proper types that can have values
//! - `k1 -> k2` (Arrow) - type constructors
//! - `Row` - effect row kind for effect polymorphism
//! - `Region` - lifetime/region kind for region polymorphism

mod primitives;
mod brrr_type;
mod func_type;
mod struct_enum;
mod scheme;
mod region;
mod kind;
mod dependent;
mod variance;

pub use primitives::{FloatPrec, IntType, ModalKind, NumericType, PrimKind, WrapperKind};
pub use brrr_type::{BrrrType, TypeId, TypeName, TypeVar};
pub use func_type::{FuncType, ParamType};
pub use struct_enum::{EnumType, FieldType, InterfaceType, MethodParam, MethodSig, StructType, VariantType};
pub use scheme::{EffectVar, ModedType, RegionedType, TypeScheme};
pub use region::{Region, ReprAttr, Variance, Visibility};
pub use kind::{
    arrow_1, arrow_2, check_kind, default_kind_env, default_kind_env_entries, extend_kind_ctx,
    infer_kind, is_proper_kind, is_proper_type, is_proper_type_with_env, is_type_constructor,
    is_type_constructor_with_env, kind_arity, kind_eq, kind_of_type, kind_result, lookup_kind,
    make_arrow_kind, Kind, KindCtx, KindedVar, NamedKindEnv, STAR,
};
pub use dependent::{
    // Core dependent types (F* DependentTypes.fsti)
    CmpOp, DepType, DepVar, Formula,
    // Capture-avoiding substitution (F* DependentTypes.fst lines 527-680)
    is_free_in_expr, find_fresh_var, fresh_var_with_base,
    free_vars_expr, free_vars_formula, free_vars_dep_type,
    alpha_rename_dep_type, alpha_rename_formula,
    subst_dep_type, subst_formula, subst_expr,
    dep_type_alpha_eq, formula_alpha_eq,
};
pub use variance::{
    // Variance system (F* Kinds.fst lines 802-1000)
    combine_variance, negate_variance,
    default_variance_env, variance_of, variance_of_param,
    VarianceEnv,
};
