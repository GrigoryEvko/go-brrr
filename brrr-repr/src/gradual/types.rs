//! Gradual typing types for AGT (Abstracting Gradual Typing)
//!
//! Implements the evidence-based blame tracking system from synthesis_part9.tex.
//!
//! # F* Specification Reference
//! ```fstar
//! type evidence =
//!   | EvRefl : gradual_type -> evidence
//!   | EvDynL : gradual_type -> evidence
//!   | EvDynR : gradual_type -> evidence
//!   | EvFunc : list evidence -> evidence -> evidence
//!   | EvRecord : list (string * evidence) -> evidence
//!
//! type evidence_result =
//!   | EvOk     : evidence -> evidence_result
//!   | EvFail   : gradual_type -> gradual_type -> evidence_result
//!
//! let rec compose_evidence (ev1 ev2: evidence) : evidence_result = ...
//! ```

use lasso::Spur;
use serde::{Deserialize, Serialize};

use crate::types::BrrrType;

/// Gradual type - types that may contain the dynamic type `?`
///
/// AGT (Abstracting Gradual Typing) treats gradual types as sets of static types,
/// where `?` represents the set of all types (universal type).
///
/// # Variants
/// - `Dynamic` - The unknown type `?`, consistent with all types
/// - `Ground(t)` - A concrete static type
/// - `GFunc` - Function type with gradual domain/codomain
/// - `GRef` - Reference to gradual type (for mutable references)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum GradualType {
    /// Dynamic type `?` - represents all possible types
    /// In AGT, gamma(?) = { all types }
    Dynamic,

    /// Ground/static type - a fully known concrete type
    /// gamma(Ground(t)) = { t }
    Ground(BrrrType),

    /// Gradual function type: (G1, G2, ...) -> G
    /// params: argument gradual types
    /// ret: return gradual type
    GFunc(Vec<GradualType>, Box<GradualType>),

    /// Gradual reference type: &G or &mut G
    /// Used for references that may point to dynamically typed values
    GRef(Box<GradualType>),
}

/// Evidence for blame tracking in gradual typing
///
/// Evidence records how type consistency was established, enabling precise
/// blame assignment when runtime type errors occur.
///
/// # F* Mapping
/// ```fstar
/// type evidence =
///   | EvRefl : gradual_type -> evidence      // Type matches itself
///   | EvDynL : gradual_type -> evidence      // Left side is dynamic
///   | EvDynR : gradual_type -> evidence      // Right side is dynamic
///   | EvFunc : list evidence -> evidence -> evidence  // Function evidence
///   | EvRecord : list (string * evidence) -> evidence // Record evidence
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Evidence {
    /// Reflexive evidence: type is consistent with itself
    /// EvRefl(G) proves G ~ G
    Refl(GradualType),

    /// Left dynamic evidence: dynamic type on left is consistent with any type
    /// EvDynL(G) proves ? ~ G
    DynL(GradualType),

    /// Right dynamic evidence: any type is consistent with dynamic type on right
    /// EvDynR(G) proves G ~ ?
    DynR(GradualType),

    /// Function evidence: combines evidence for parameters and return type
    /// EvFunc([ev1, ..., evn], ev_ret) proves (G1 -> R1) ~ (G2 -> R2)
    /// where evi proves Gi2 ~ Gi1 (contravariant) and ev_ret proves R1 ~ R2 (covariant)
    Func(Vec<Evidence>, Box<Evidence>),

    /// Record evidence: evidence for each field
    /// EvRecord([(f1, ev1), ...]) proves {f1: T1, ...} ~ {f1: S1, ...}
    Record(Vec<(Spur, Evidence)>),
}

/// Result of evidence composition
///
/// Evidence composition may fail when the evidence witnesses incompatible
/// type transitions (e.g., ? -> Int composed with String -> ?).
///
/// # F* Mapping
/// ```fstar
/// type evidence_result =
///   | EvOk     : evidence -> evidence_result
///   | EvFail   : gradual_type -> gradual_type -> evidence_result
/// ```
#[derive(Debug, Clone, PartialEq)]
pub enum EvidenceResult {
    /// Composition succeeded, producing new evidence
    Ok(Evidence),

    /// Composition failed due to type mismatch
    /// `from` is the source type, `to` is the incompatible target type
    Fail {
        from: GradualType,
        to: GradualType,
    },
}

impl EvidenceResult {
    /// Check if composition succeeded
    #[inline]
    pub const fn is_ok(&self) -> bool {
        matches!(self, Self::Ok(_))
    }

    /// Check if composition failed
    #[inline]
    pub const fn is_fail(&self) -> bool {
        matches!(self, Self::Fail { .. })
    }

    /// Extract evidence if composition succeeded
    #[inline]
    pub fn ok(self) -> Option<Evidence> {
        match self {
            Self::Ok(ev) => Some(ev),
            Self::Fail { .. } => None,
        }
    }

    /// Extract blame types if composition failed
    #[inline]
    pub fn fail(self) -> Option<(GradualType, GradualType)> {
        match self {
            Self::Ok(_) => None,
            Self::Fail { from, to } => Some((from, to)),
        }
    }
}

/// Compose two pieces of evidence
///
/// Implements evidence composition for gradual typing blame tracking.
/// If `ev1` witnesses `G1 ~ G2` and `ev2` witnesses `G2 ~ G3`, then
/// composition produces evidence for `G1 ~ G3` (if compatible).
///
/// # Composition Rules (from F* spec)
///
/// - `Refl(G) ∘ ev = ev` (identity left)
/// - `ev ∘ Refl(G) = ev` (identity right)
/// - `DynL(G1) ∘ DynR(G2) = Refl(G1)` if G1 ~ G2, else Fail
/// - `DynR(G1) ∘ DynL(G2) = Refl(G2)` if G1 ~ G2, else Fail
/// - `Func(evs1, ret1) ∘ Func(evs2, ret2)`:
///   - Args composed contravariantly (reversed order)
///   - Return composed covariantly
/// - `Record(fs1) ∘ Record(fs2)`: compose field-wise
///
/// # Returns
///
/// - `EvidenceResult::Ok(ev)` if composition succeeds
/// - `EvidenceResult::Fail { from, to }` with blame info if types are incompatible
pub fn compose_evidence(ev1: &Evidence, ev2: &Evidence) -> EvidenceResult {
    match (ev1, ev2) {
        // Identity: Refl is neutral element for composition
        (Evidence::Refl(_), ev) => EvidenceResult::Ok(ev.clone()),
        (ev, Evidence::Refl(_)) => EvidenceResult::Ok(ev.clone()),

        // DynL ∘ DynR: ? -> G1 composed with G2 -> ?
        // The intermediate types G1 and G2 must be consistent
        (Evidence::DynL(g1), Evidence::DynR(g2)) => {
            if g1.is_consistent_with(g2) {
                EvidenceResult::Ok(Evidence::Refl(g1.clone()))
            } else {
                EvidenceResult::Fail {
                    from: g1.clone(),
                    to: g2.clone(),
                }
            }
        }

        // DynR ∘ DynL: G1 -> ? composed with ? -> G2
        // The intermediate types must be consistent
        (Evidence::DynR(g1), Evidence::DynL(g2)) => {
            if g1.is_consistent_with(g2) {
                EvidenceResult::Ok(Evidence::Refl(g2.clone()))
            } else {
                EvidenceResult::Fail {
                    from: g1.clone(),
                    to: g2.clone(),
                }
            }
        }

        // DynL ∘ DynL: ? -> G1 composed with ? -> G2
        // Both evidence pieces have dynamic source, pick target of second
        (Evidence::DynL(_), Evidence::DynL(g2)) => {
            EvidenceResult::Ok(Evidence::DynL(g2.clone()))
        }

        // DynR ∘ DynR: G1 -> ? composed with G2 -> ?
        // Both have dynamic target, keep source of first
        (Evidence::DynR(g1), Evidence::DynR(_)) => {
            EvidenceResult::Ok(Evidence::DynR(g1.clone()))
        }

        // Function composition: contravariant in args, covariant in return
        (Evidence::Func(args1, ret1), Evidence::Func(args2, ret2)) => {
            if args1.len() != args2.len() {
                return EvidenceResult::Fail {
                    from: ev1.source(),
                    to: ev2.target(),
                };
            }

            // Compose arguments (contravariant: compose in reversed order)
            // F* spec: args' = List.map2 compose_evidence (List.rev args2) (List.rev args1)
            let mut composed_args = Vec::with_capacity(args1.len());
            for (a2, a1) in args2.iter().zip(args1.iter()) {
                match compose_evidence(a2, a1) {
                    EvidenceResult::Ok(ev) => composed_args.push(ev),
                    fail @ EvidenceResult::Fail { .. } => return fail,
                }
            }

            // Compose return type (covariant)
            match compose_evidence(ret1.as_ref(), ret2.as_ref()) {
                EvidenceResult::Ok(ret_ev) => {
                    EvidenceResult::Ok(Evidence::Func(composed_args, Box::new(ret_ev)))
                }
                fail @ EvidenceResult::Fail { .. } => fail,
            }
        }

        // Record composition: compose field-wise
        (Evidence::Record(fs1), Evidence::Record(fs2)) => {
            if fs1.len() != fs2.len() {
                return EvidenceResult::Fail {
                    from: ev1.source(),
                    to: ev2.target(),
                };
            }

            let mut composed_fields = Vec::with_capacity(fs1.len());
            for ((name1, ev_f1), (name2, ev_f2)) in fs1.iter().zip(fs2.iter()) {
                if name1 != name2 {
                    return EvidenceResult::Fail {
                        from: ev1.source(),
                        to: ev2.target(),
                    };
                }
                match compose_evidence(ev_f1, ev_f2) {
                    EvidenceResult::Ok(ev) => composed_fields.push((*name1, ev)),
                    fail @ EvidenceResult::Fail { .. } => return fail,
                }
            }

            EvidenceResult::Ok(Evidence::Record(composed_fields))
        }

        // Incompatible evidence kinds
        _ => EvidenceResult::Fail {
            from: ev1.source(),
            to: ev2.target(),
        },
    }
}

/// Result of concretizing a gradual type to a set of static types
///
/// Since we cannot represent infinite sets directly, we use an ADT to
/// describe the structure of the concretization set.
///
/// # F* Specification
/// ```fstar
/// let rec gamma_gradual (g: gradual_type) : set static_type =
///   match g with
///   | GTDynamic -> all_static_types  (* Universal set *)
///   | GTGround t -> singleton t
///   | GTFunc params ret ->
///       { TFunc ps r | ps in cross_product (map gamma_gradual params),
///                      r in gamma_gradual ret }
///   | GTRef t -> { TRef t' | t' in gamma_gradual t }
/// ```
#[derive(Debug, Clone, PartialEq)]
pub enum ConcretizationResult {
    /// Infinite set representing all possible static types
    /// Corresponds to `gamma(?) = all_static_types`
    Infinite,

    /// Finite set of concrete static types
    /// Corresponds to `gamma(Ground(t)) = { t }`
    Finite(Vec<BrrrType>),

    /// Function type set: cross product of param sets and return set
    /// `{ TFunc ps r | ps in cross_product(param_sets), r in ret_set }`
    FuncSet {
        params: Vec<ConcretizationResult>,
        ret: Box<ConcretizationResult>,
    },

    /// Reference type set: `{ TRef t' | t' in inner_set }`
    RefSet(Box<ConcretizationResult>),
}

impl ConcretizationResult {
    /// Check if this represents an infinite set
    #[inline]
    pub fn is_infinite(&self) -> bool {
        match self {
            Self::Infinite => true,
            Self::Finite(_) => false,
            Self::FuncSet { params, ret } => {
                params.iter().any(Self::is_infinite) || ret.is_infinite()
            }
            Self::RefSet(inner) => inner.is_infinite(),
        }
    }

    /// Check if this represents a singleton set
    pub fn is_singleton(&self) -> bool {
        match self {
            Self::Infinite => false,
            Self::Finite(types) => types.len() == 1,
            Self::FuncSet { params, ret } => {
                params.iter().all(Self::is_singleton) && ret.is_singleton()
            }
            Self::RefSet(inner) => inner.is_singleton(),
        }
    }

    /// Check if this represents an empty set
    pub fn is_empty(&self) -> bool {
        match self {
            Self::Infinite => false,
            Self::Finite(types) => types.is_empty(),
            Self::FuncSet { params, ret } => {
                params.iter().any(Self::is_empty) || ret.is_empty()
            }
            Self::RefSet(inner) => inner.is_empty(),
        }
    }

    /// Check if two concretization results have non-empty intersection
    ///
    /// This is the semantic basis for type consistency in AGT:
    /// `G1 ~ G2` iff `gamma(G1) ∩ gamma(G2) =/= empty`
    pub fn intersects(&self, other: &Self) -> bool {
        match (self, other) {
            // Infinite set intersects with any non-empty set
            (Self::Infinite, other) | (other, Self::Infinite) => !other.is_empty(),

            // Two finite sets intersect if they share any element
            (Self::Finite(a), Self::Finite(b)) => a.iter().any(|t| b.contains(t)),

            // Function sets intersect if params and returns intersect
            (
                Self::FuncSet {
                    params: p1,
                    ret: r1,
                },
                Self::FuncSet {
                    params: p2,
                    ret: r2,
                },
            ) => {
                if p1.len() != p2.len() {
                    return false;
                }
                p1.iter()
                    .zip(p2.iter())
                    .all(|(a, b)| a.intersects(b))
                    && r1.intersects(r2)
            }

            // Reference sets intersect if their inner sets intersect
            (Self::RefSet(a), Self::RefSet(b)) => a.intersects(b),

            // Mismatched shapes do not intersect
            _ => false,
        }
    }
}

impl GradualType {
    /// Create a dynamic type (unknown type `?`)
    #[inline]
    pub const fn dynamic() -> Self {
        Self::Dynamic
    }

    /// Create a ground type from a static type
    #[inline]
    pub fn ground(ty: BrrrType) -> Self {
        Self::Ground(ty)
    }

    /// Create a gradual type from a literal
    pub fn from_literal(lit: &crate::expr::Literal) -> Self {
        use crate::expr::Literal;
        use crate::types::NumericType;

        let ty = match lit {
            Literal::Unit => BrrrType::UNIT,
            Literal::Bool(_) => BrrrType::BOOL,
            Literal::Char(_) => BrrrType::CHAR,
            Literal::String(_) => BrrrType::STRING,
            Literal::Int(_, int_ty) => BrrrType::Numeric(NumericType::Int(*int_ty)),
            Literal::Float(_, float_prec) => BrrrType::Numeric(NumericType::Float(*float_prec)),
        };
        Self::Ground(ty)
    }

    /// Create a gradual function type
    #[inline]
    pub fn func(params: Vec<GradualType>, ret: GradualType) -> Self {
        Self::GFunc(params, Box::new(ret))
    }

    /// Create a gradual reference type
    #[inline]
    pub fn reference(inner: GradualType) -> Self {
        Self::GRef(Box::new(inner))
    }

    /// Check if this is the dynamic type `?`
    #[inline]
    pub const fn is_dynamic(&self) -> bool {
        matches!(self, Self::Dynamic)
    }

    /// Check if this type contains any dynamic components
    ///
    /// Returns true if the type is `?` or contains `?` in any subtype.
    pub fn contains_dynamic(&self) -> bool {
        match self {
            Self::Dynamic => true,
            Self::Ground(_) => false,
            Self::GFunc(params, ret) => {
                params.iter().any(Self::contains_dynamic) || ret.contains_dynamic()
            }
            Self::GRef(inner) => inner.contains_dynamic(),
        }
    }

    /// Check if this is a fully static type (no dynamic components)
    #[inline]
    pub fn is_static(&self) -> bool {
        !self.contains_dynamic()
    }

    /// Extract static type if this is a ground type with no dynamic components
    ///
    /// Returns `Some(ty)` if the gradual type is `Ground(ty)` and `ty` itself
    /// contains no dynamic components. Returns `None` for `Dynamic`, `GFunc`,
    /// or `GRef` types.
    pub fn static_type(&self) -> Option<&BrrrType> {
        match self {
            Self::Ground(ty) => Some(ty),
            Self::Dynamic | Self::GFunc(_, _) | Self::GRef(_) => None,
        }
    }

    /// Convert to static type, consuming self
    ///
    /// Returns `Some(ty)` only for `Ground(ty)`.
    pub fn into_static_type(self) -> Option<BrrrType> {
        match self {
            Self::Ground(ty) => Some(ty),
            Self::Dynamic | Self::GFunc(_, _) | Self::GRef(_) => None,
        }
    }

    /// Check type consistency (G1 ~ G2)
    ///
    /// In AGT, two gradual types are consistent if their concretizations overlap:
    /// `G1 ~ G2` iff `gamma(G1) ∩ gamma(G2) ≠ ∅`
    ///
    /// Key rules:
    /// - `? ~ G` for any G (dynamic is consistent with everything)
    /// - `G ~ ?` for any G
    /// - `Ground(T1) ~ Ground(T2)` iff T1 = T2
    /// - `(G1 -> R1) ~ (G2 -> R2)` iff G1 ~ G2 and R1 ~ R2
    ///
    /// Note: Consistency is reflexive and symmetric but NOT transitive.
    pub fn is_consistent_with(&self, other: &Self) -> bool {
        match (self, other) {
            // Dynamic is consistent with everything
            (Self::Dynamic, _) | (_, Self::Dynamic) => true,

            // Ground types must be equal
            (Self::Ground(t1), Self::Ground(t2)) => t1 == t2,

            // Function types: consistent element-wise
            (Self::GFunc(params1, ret1), Self::GFunc(params2, ret2)) => {
                params1.len() == params2.len()
                    && params1
                        .iter()
                        .zip(params2.iter())
                        .all(|(p1, p2)| p1.is_consistent_with(p2))
                    && ret1.is_consistent_with(ret2)
            }

            // Reference types: consistent if inner types are consistent
            (Self::GRef(inner1), Self::GRef(inner2)) => inner1.is_consistent_with(inner2),

            // Mismatched type constructors are inconsistent
            _ => false,
        }
    }

    /// Alias for `is_consistent_with` matching F* spec naming
    ///
    /// # F* Specification
    /// ```fstar
    /// let rec type_consistent (g1 g2: gradual_type) : bool =
    ///   match g1, g2 with
    ///   | GTDynamic, _ -> true
    ///   | _, GTDynamic -> true
    ///   | GTGround t1, GTGround t2 -> t1 = t2
    ///   | GTFunc params1 ret1, GTFunc params2 ret2 ->
    ///       List.length params1 = List.length params2 &&
    ///       List.for_all2 type_consistent params1 params2 &&
    ///       type_consistent ret1 ret2
    ///   | GTRef t1, GTRef t2 -> type_consistent t1 t2
    ///   | _, _ -> false
    /// ```
    #[inline]
    pub fn is_consistent(&self, other: &Self) -> bool {
        self.is_consistent_with(other)
    }

    /// Compute the concretization of this gradual type
    ///
    /// Maps a gradual type to its set of possible static types.
    /// Since sets can be infinite (for Dynamic), we return a structured
    /// representation rather than an actual set.
    ///
    /// # F* Specification
    /// ```fstar
    /// let rec gamma_gradual (g: gradual_type) : set static_type =
    ///   match g with
    ///   | GTDynamic -> all_static_types
    ///   | GTGround t -> singleton t
    ///   | GTFunc params ret ->
    ///       { TFunc ps r | ps in cross_product (map gamma_gradual params),
    ///                      r in gamma_gradual ret }
    ///   | GTRef t -> { TRef t' | t' in gamma_gradual t }
    /// ```
    pub fn concretize(&self) -> ConcretizationResult {
        match self {
            Self::Dynamic => ConcretizationResult::Infinite,

            Self::Ground(ty) => ConcretizationResult::Finite(vec![ty.clone()]),

            Self::GFunc(params, ret) => ConcretizationResult::FuncSet {
                params: params.iter().map(Self::concretize).collect(),
                ret: Box::new(ret.concretize()),
            },

            Self::GRef(inner) => ConcretizationResult::RefSet(Box::new(inner.concretize())),
        }
    }

    /// Check if this type is at least as precise as another (precision ordering)
    ///
    /// The precision relation forms a partial order where Dynamic is the
    /// least precise type (top of the lattice). A type G1 is more precise
    /// than G2 if `gamma(G1) ⊆ gamma(G2)`.
    ///
    /// # Properties
    /// - `G ⊑ ?` for all G (Dynamic is top)
    /// - `Ground(T) ⊑ Ground(T)` (reflexive on ground types)
    /// - If all param/return types are more precise, function is more precise
    ///
    /// # Examples
    /// - `Bool.precision_leq(?)` = true (Bool is more precise than Dynamic)
    /// - `?.precision_leq(Bool)` = false (Dynamic is not more precise than Bool)
    /// - `(Bool) -> Int ⊑ (?) -> ?`
    pub fn precision_leq(&self, other: &Self) -> bool {
        match (self, other) {
            // Everything is less precise than or equal to Dynamic
            (_, Self::Dynamic) => true,

            // Dynamic is only less precise than itself
            (Self::Dynamic, _) => false,

            // Ground types: reflexive only (must be equal)
            (Self::Ground(t1), Self::Ground(t2)) => t1 == t2,

            // Function precision: covariant throughout for set inclusion
            (Self::GFunc(params1, ret1), Self::GFunc(params2, ret2)) => {
                params1.len() == params2.len()
                    && params1
                        .iter()
                        .zip(params2.iter())
                        .all(|(p1, p2)| p1.precision_leq(p2))
                    && ret1.precision_leq(ret2)
            }

            // Reference precision: covariant in inner type
            (Self::GRef(t1), Self::GRef(t2)) => t1.precision_leq(t2),

            // Mismatched constructors: not comparable (false)
            _ => false,
        }
    }

    /// Compute the greatest lower bound (meet) of two gradual types
    ///
    /// The meet operation finds the most general type that is more precise
    /// than both inputs. Returns None if no such type exists (types are
    /// inconsistent at some point).
    ///
    /// # Properties
    /// - `meet(G, ?) = Some(G)` (Dynamic is top)
    /// - `meet(?, G) = Some(G)`
    /// - `meet(Ground(T), Ground(T)) = Some(Ground(T))`
    /// - `meet(Ground(T1), Ground(T2)) = None` if T1 != T2
    ///
    /// # Examples
    /// - `meet(Bool, ?) = Some(Bool)`
    /// - `meet(Bool, Int) = None`
    /// - `meet((?) -> Bool, (Int) -> ?) = Some((Int) -> Bool)`
    pub fn meet(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            // Meet with Dynamic returns the other type
            (Self::Dynamic, other) => Some(other.clone()),
            (this, Self::Dynamic) => Some(this.clone()),

            // Ground types: must be equal
            (Self::Ground(t1), Self::Ground(t2)) => {
                if t1 == t2 {
                    Some(Self::Ground(t1.clone()))
                } else {
                    None
                }
            }

            // Function types: meet component-wise
            (Self::GFunc(params1, ret1), Self::GFunc(params2, ret2)) => {
                if params1.len() != params2.len() {
                    return None;
                }

                let meet_params: Option<Vec<_>> = params1
                    .iter()
                    .zip(params2.iter())
                    .map(|(p1, p2)| p1.meet(p2))
                    .collect();

                let meet_ret = ret1.meet(ret2)?;

                Some(Self::GFunc(meet_params?, Box::new(meet_ret)))
            }

            // Reference types: meet inner
            (Self::GRef(t1), Self::GRef(t2)) => {
                let meet_inner = t1.meet(t2)?;
                Some(Self::GRef(Box::new(meet_inner)))
            }

            // Mismatched constructors: no meet
            _ => None,
        }
    }

    /// Compute the least upper bound (join) of two gradual types
    ///
    /// The join operation finds the least precise type that is at least as
    /// precise as both inputs. Returns None if types are structurally
    /// incompatible (different constructors with non-Dynamic base).
    ///
    /// # Properties
    /// - `join(G, ?) = ?`
    /// - `join(?, G) = ?`
    /// - `join(Ground(T), Ground(T)) = Ground(T)`
    /// - `join(Ground(T1), Ground(T2)) = ?` if T1 != T2
    pub fn join(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            // Join with Dynamic returns Dynamic
            (Self::Dynamic, _) | (_, Self::Dynamic) => Some(Self::Dynamic),

            // Ground types: equal -> same, different -> Dynamic
            (Self::Ground(t1), Self::Ground(t2)) => {
                if t1 == t2 {
                    Some(Self::Ground(t1.clone()))
                } else {
                    Some(Self::Dynamic)
                }
            }

            // Function types: join component-wise
            (Self::GFunc(params1, ret1), Self::GFunc(params2, ret2)) => {
                if params1.len() != params2.len() {
                    return None;
                }

                let join_params: Option<Vec<_>> = params1
                    .iter()
                    .zip(params2.iter())
                    .map(|(p1, p2)| p1.join(p2))
                    .collect();

                let join_ret = ret1.join(ret2)?;

                Some(Self::GFunc(join_params?, Box::new(join_ret)))
            }

            // Reference types: join inner
            (Self::GRef(t1), Self::GRef(t2)) => {
                let join_inner = t1.join(t2)?;
                Some(Self::GRef(Box::new(join_inner)))
            }

            // Mismatched constructors: no join (structurally incompatible)
            _ => None,
        }
    }
}

impl Evidence {
    /// Create reflexive evidence for a type consistent with itself
    #[inline]
    pub fn refl(ty: GradualType) -> Self {
        Self::Refl(ty)
    }

    /// Create evidence for dynamic type on the left
    #[inline]
    pub fn dyn_left(ty: GradualType) -> Self {
        Self::DynL(ty)
    }

    /// Create evidence for dynamic type on the right
    #[inline]
    pub fn dyn_right(ty: GradualType) -> Self {
        Self::DynR(ty)
    }

    /// Create function evidence from parameter and return evidence
    #[inline]
    pub fn func(params: Vec<Evidence>, ret: Evidence) -> Self {
        Self::Func(params, Box::new(ret))
    }

    /// Create record evidence from field evidence pairs
    #[inline]
    pub fn record(fields: Vec<(Spur, Evidence)>) -> Self {
        Self::Record(fields)
    }

    /// Check if this evidence involves any dynamic type casts
    ///
    /// Returns true if the evidence tree contains DynL or DynR nodes,
    /// indicating that runtime checks may be needed.
    pub fn involves_dynamic(&self) -> bool {
        match self {
            Self::Refl(_) => false,
            Self::DynL(_) | Self::DynR(_) => true,
            Self::Func(params, ret) => {
                params.iter().any(Self::involves_dynamic) || ret.involves_dynamic()
            }
            Self::Record(fields) => fields.iter().any(|(_, ev)| ev.involves_dynamic()),
        }
    }

    /// Check if this is pure reflexive evidence (no casts needed)
    #[inline]
    pub fn is_reflexive(&self) -> bool {
        matches!(self, Self::Refl(_))
    }

    /// Extract the source type from this evidence
    ///
    /// For evidence proving `G1 ~ G2`, returns G1.
    ///
    /// # Evidence Type Mappings
    /// - `Refl(G)` proves `G ~ G`, source is G
    /// - `DynL(G)` proves `? ~ G`, source is `?`
    /// - `DynR(G)` proves `G ~ ?`, source is G
    /// - `Func(evs, ev)` proves `(S1,...,Sn) -> R1 ~ (T1,...,Tn) -> R2`
    /// - `Record(fs)` proves `{f1: S1, ...} ~ {f1: T1, ...}`
    pub fn source(&self) -> GradualType {
        match self {
            Self::Refl(g) => g.clone(),
            Self::DynL(_) => GradualType::Dynamic,
            Self::DynR(g) => g.clone(),
            Self::Func(params, ret) => {
                let param_sources: Vec<_> = params.iter().map(Evidence::source).collect();
                let ret_source = ret.source();
                GradualType::GFunc(param_sources, Box::new(ret_source))
            }
            Self::Record(fields) => {
                // For records, we cannot fully reconstruct the type without field names
                // Return Dynamic as a conservative approximation
                // A complete implementation would need the BrrrType::Record variant
                if fields.is_empty() {
                    GradualType::Dynamic
                } else {
                    GradualType::Dynamic
                }
            }
        }
    }

    /// Extract the target type from this evidence
    ///
    /// For evidence proving `G1 ~ G2`, returns G2.
    ///
    /// # Evidence Type Mappings
    /// - `Refl(G)` proves `G ~ G`, target is G
    /// - `DynL(G)` proves `? ~ G`, target is G
    /// - `DynR(G)` proves `G ~ ?`, target is `?`
    /// - `Func(evs, ev)` proves `(S1,...,Sn) -> R1 ~ (T1,...,Tn) -> R2`
    /// - `Record(fs)` proves `{f1: S1, ...} ~ {f1: T1, ...}`
    pub fn target(&self) -> GradualType {
        match self {
            Self::Refl(g) => g.clone(),
            Self::DynL(g) => g.clone(),
            Self::DynR(_) => GradualType::Dynamic,
            Self::Func(params, ret) => {
                let param_targets: Vec<_> = params.iter().map(Evidence::target).collect();
                let ret_target = ret.target();
                GradualType::GFunc(param_targets, Box::new(ret_target))
            }
            Self::Record(fields) => {
                // Conservative approximation for records
                if fields.is_empty() {
                    GradualType::Dynamic
                } else {
                    GradualType::Dynamic
                }
            }
        }
    }

    /// Invert the direction of this evidence
    ///
    /// If `ev` proves `G1 ~ G2`, then `ev.invert()` proves `G2 ~ G1`.
    ///
    /// # Inversion Rules
    /// - `Refl(G).invert() = Refl(G)` (symmetric)
    /// - `DynL(G).invert() = DynR(G)` (swap direction)
    /// - `DynR(G).invert() = DynL(G)` (swap direction)
    /// - `Func(evs, ev).invert() = Func(evs.map(invert), ev.invert())`
    /// - `Record(fs).invert() = Record(fs.map(invert))`
    pub fn invert(&self) -> Self {
        match self {
            Self::Refl(g) => Self::Refl(g.clone()),
            Self::DynL(g) => Self::DynR(g.clone()),
            Self::DynR(g) => Self::DynL(g.clone()),
            Self::Func(params, ret) => {
                let inverted_params: Vec<_> = params.iter().map(Evidence::invert).collect();
                let inverted_ret = ret.invert();
                Self::Func(inverted_params, Box::new(inverted_ret))
            }
            Self::Record(fields) => {
                let inverted_fields: Vec<_> = fields
                    .iter()
                    .map(|(name, ev)| (*name, ev.invert()))
                    .collect();
                Self::Record(inverted_fields)
            }
        }
    }

    /// Compose two pieces of evidence
    ///
    /// If `ev1` proves `G1 ~ G2` and `ev2` proves `G2 ~ G3`, then
    /// `compose(ev1, ev2)` proves `G1 ~ G3` (if composition succeeds).
    ///
    /// Composition may fail if the intermediate types are incompatible,
    /// resulting in blame information indicating which types conflicted.
    ///
    /// # F* Specification
    /// ```fstar
    /// let rec compose_evidence (ev1 ev2: evidence) : evidence_result =
    ///   match ev1, ev2 with
    ///   | EvRefl g, ev -> EvOk ev
    ///   | ev, EvRefl g -> EvOk ev
    ///   | EvDynL g1, EvDynR g2 ->
    ///       if type_consistent g1 g2 then EvOk (EvRefl g1)
    ///       else EvFail g1 g2
    ///   | ...
    /// ```
    pub fn compose(&self, other: &Self) -> EvidenceResult {
        crate::gradual::types::compose_evidence(self, other)
    }
}

impl From<BrrrType> for GradualType {
    fn from(ty: BrrrType) -> Self {
        Self::Ground(ty)
    }
}

impl Default for GradualType {
    /// Default gradual type is Dynamic (unknown)
    fn default() -> Self {
        Self::Dynamic
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::PrimKind;

    #[test]
    fn test_gradual_type_constructors() {
        let dyn_ty = GradualType::dynamic();
        assert!(dyn_ty.is_dynamic());
        assert!(dyn_ty.contains_dynamic());
        assert!(!dyn_ty.is_static());

        let ground = GradualType::ground(BrrrType::BOOL);
        assert!(!ground.is_dynamic());
        assert!(!ground.contains_dynamic());
        assert!(ground.is_static());
        assert_eq!(ground.static_type(), Some(&BrrrType::BOOL));

        let func = GradualType::func(vec![GradualType::dynamic()], GradualType::ground(BrrrType::BOOL));
        assert!(!func.is_dynamic());
        assert!(func.contains_dynamic());
        assert!(!func.is_static());
    }

    #[test]
    fn test_static_type_extraction() {
        let ground = GradualType::ground(BrrrType::Prim(PrimKind::String));
        assert_eq!(ground.static_type(), Some(&BrrrType::Prim(PrimKind::String)));

        let dyn_ty = GradualType::dynamic();
        assert_eq!(dyn_ty.static_type(), None);

        let func = GradualType::func(vec![], GradualType::ground(BrrrType::UNIT));
        assert_eq!(func.static_type(), None);
    }

    #[test]
    fn test_evidence_constructors() {
        let refl = Evidence::refl(GradualType::ground(BrrrType::BOOL));
        assert!(refl.is_reflexive());
        assert!(!refl.involves_dynamic());

        let dyn_l = Evidence::dyn_left(GradualType::ground(BrrrType::BOOL));
        assert!(!dyn_l.is_reflexive());
        assert!(dyn_l.involves_dynamic());

        let dyn_r = Evidence::dyn_right(GradualType::ground(BrrrType::BOOL));
        assert!(!dyn_r.is_reflexive());
        assert!(dyn_r.involves_dynamic());
    }

    #[test]
    fn test_function_evidence() {
        let func_ev = Evidence::func(
            vec![Evidence::refl(GradualType::ground(BrrrType::BOOL))],
            Evidence::dyn_left(GradualType::ground(BrrrType::STRING)),
        );
        assert!(!func_ev.is_reflexive());
        assert!(func_ev.involves_dynamic());

        let pure_func = Evidence::func(
            vec![Evidence::refl(GradualType::ground(BrrrType::BOOL))],
            Evidence::refl(GradualType::ground(BrrrType::STRING)),
        );
        assert!(!pure_func.is_reflexive());
        assert!(!pure_func.involves_dynamic());
    }

    #[test]
    fn test_gradual_type_from_brrr() {
        let brrr_ty = BrrrType::BOOL;
        let gradual: GradualType = brrr_ty.into();
        assert!(matches!(gradual, GradualType::Ground(BrrrType::Prim(PrimKind::Bool))));
    }

    #[test]
    fn test_type_consistency() {
        let dyn_ty = GradualType::dynamic();
        let bool_ty = GradualType::ground(BrrrType::BOOL);
        let int_ty = GradualType::ground(BrrrType::Numeric(crate::types::NumericType::Int(crate::types::IntType::I32)));

        // Dynamic is consistent with everything
        assert!(dyn_ty.is_consistent(&bool_ty));
        assert!(bool_ty.is_consistent(&dyn_ty));
        assert!(dyn_ty.is_consistent(&dyn_ty));

        // Same ground types are consistent
        assert!(bool_ty.is_consistent(&bool_ty));

        // Different ground types are not consistent
        assert!(!bool_ty.is_consistent(&int_ty));

        // Function type consistency
        let func1 = GradualType::func(vec![bool_ty.clone()], int_ty.clone());
        let func2 = GradualType::func(vec![dyn_ty.clone()], dyn_ty.clone());
        let func3 = GradualType::func(vec![int_ty.clone()], bool_ty.clone());

        assert!(func1.is_consistent(&func2)); // ? matches anything
        assert!(!func1.is_consistent(&func3)); // Bool != Int in params

        // Reference type consistency
        let ref1 = GradualType::reference(bool_ty.clone());
        let ref2 = GradualType::reference(dyn_ty.clone());
        let ref3 = GradualType::reference(int_ty.clone());

        assert!(ref1.is_consistent(&ref2));
        assert!(!ref1.is_consistent(&ref3));
    }

    #[test]
    fn test_concretization() {
        let dyn_ty = GradualType::dynamic();
        let bool_ty = GradualType::ground(BrrrType::BOOL);

        // Dynamic concretizes to infinite set
        let conc_dyn = dyn_ty.concretize();
        assert!(conc_dyn.is_infinite());
        assert!(!conc_dyn.is_singleton());

        // Ground type concretizes to singleton
        let conc_bool = bool_ty.concretize();
        assert!(!conc_bool.is_infinite());
        assert!(conc_bool.is_singleton());

        // Function type concretization
        let func = GradualType::func(vec![dyn_ty.clone()], bool_ty.clone());
        let conc_func = func.concretize();
        assert!(conc_func.is_infinite()); // Param is infinite

        let static_func = GradualType::func(vec![bool_ty.clone()], bool_ty.clone());
        let conc_static = static_func.concretize();
        assert!(!conc_static.is_infinite());
        assert!(conc_static.is_singleton());
    }

    #[test]
    fn test_concretization_intersects() {
        let bool_conc = ConcretizationResult::Finite(vec![BrrrType::BOOL]);
        let string_conc = ConcretizationResult::Finite(vec![BrrrType::STRING]);
        let infinite = ConcretizationResult::Infinite;

        // Same finite sets intersect
        assert!(bool_conc.intersects(&bool_conc));

        // Different finite sets don't intersect
        assert!(!bool_conc.intersects(&string_conc));

        // Infinite intersects with everything
        assert!(infinite.intersects(&bool_conc));
        assert!(bool_conc.intersects(&infinite));

        // Empty set doesn't intersect with infinite
        let empty = ConcretizationResult::Finite(vec![]);
        assert!(!empty.intersects(&infinite));
    }

    #[test]
    fn test_precision_ordering() {
        let dyn_ty = GradualType::dynamic();
        let bool_ty = GradualType::ground(BrrrType::BOOL);
        let int_ty = GradualType::ground(BrrrType::Numeric(crate::types::NumericType::Int(crate::types::IntType::I32)));

        // Everything is less precise than Dynamic
        assert!(bool_ty.precision_leq(&dyn_ty));
        assert!(int_ty.precision_leq(&dyn_ty));
        assert!(dyn_ty.precision_leq(&dyn_ty));

        // Dynamic is not more precise than ground types
        assert!(!dyn_ty.precision_leq(&bool_ty));

        // Same ground types are equally precise
        assert!(bool_ty.precision_leq(&bool_ty));

        // Different ground types are not comparable
        assert!(!bool_ty.precision_leq(&int_ty));
        assert!(!int_ty.precision_leq(&bool_ty));

        // Function type precision
        let static_func = GradualType::func(vec![bool_ty.clone()], int_ty.clone());
        let dyn_func = GradualType::func(vec![dyn_ty.clone()], dyn_ty.clone());

        assert!(static_func.precision_leq(&dyn_func));
        assert!(!dyn_func.precision_leq(&static_func));
    }

    #[test]
    fn test_meet() {
        let dyn_ty = GradualType::dynamic();
        let bool_ty = GradualType::ground(BrrrType::BOOL);
        let int_ty = GradualType::ground(BrrrType::Numeric(crate::types::NumericType::Int(crate::types::IntType::I32)));

        // Meet with Dynamic returns the other type
        assert_eq!(dyn_ty.meet(&bool_ty), Some(bool_ty.clone()));
        assert_eq!(bool_ty.meet(&dyn_ty), Some(bool_ty.clone()));

        // Meet of same ground types returns that type
        assert_eq!(bool_ty.meet(&bool_ty), Some(bool_ty.clone()));

        // Meet of different ground types is None
        assert_eq!(bool_ty.meet(&int_ty), None);

        // Function type meet
        let func1 = GradualType::func(vec![dyn_ty.clone()], bool_ty.clone());
        let func2 = GradualType::func(vec![int_ty.clone()], dyn_ty.clone());
        let expected = GradualType::func(vec![int_ty.clone()], bool_ty.clone());

        assert_eq!(func1.meet(&func2), Some(expected));
    }

    #[test]
    fn test_join() {
        let dyn_ty = GradualType::dynamic();
        let bool_ty = GradualType::ground(BrrrType::BOOL);
        let int_ty = GradualType::ground(BrrrType::Numeric(crate::types::NumericType::Int(crate::types::IntType::I32)));

        // Join with Dynamic returns Dynamic
        assert_eq!(dyn_ty.join(&bool_ty), Some(dyn_ty.clone()));
        assert_eq!(bool_ty.join(&dyn_ty), Some(dyn_ty.clone()));

        // Join of same ground types returns that type
        assert_eq!(bool_ty.join(&bool_ty), Some(bool_ty.clone()));

        // Join of different ground types is Dynamic
        assert_eq!(bool_ty.join(&int_ty), Some(dyn_ty.clone()));

        // Function type join
        let func1 = GradualType::func(vec![bool_ty.clone()], int_ty.clone());
        let func2 = GradualType::func(vec![int_ty.clone()], bool_ty.clone());
        let expected = GradualType::func(vec![dyn_ty.clone()], dyn_ty.clone());

        assert_eq!(func1.join(&func2), Some(expected));
    }

    #[test]
    fn test_evidence_source_target() {
        let bool_ty = GradualType::ground(BrrrType::BOOL);
        let int_ty = GradualType::ground(BrrrType::Numeric(crate::types::NumericType::Int(crate::types::IntType::I64)));

        let refl = Evidence::refl(bool_ty.clone());
        assert_eq!(refl.source(), bool_ty);
        assert_eq!(refl.target(), bool_ty);

        let dyn_l = Evidence::dyn_left(int_ty.clone());
        assert_eq!(dyn_l.source(), GradualType::Dynamic);
        assert_eq!(dyn_l.target(), int_ty);

        let dyn_r = Evidence::dyn_right(bool_ty.clone());
        assert_eq!(dyn_r.source(), bool_ty);
        assert_eq!(dyn_r.target(), GradualType::Dynamic);

        let func_ev = Evidence::func(
            vec![Evidence::refl(bool_ty.clone())],
            Evidence::dyn_left(int_ty.clone()),
        );
        match func_ev.source() {
            GradualType::GFunc(params, ret) => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0], bool_ty);
                assert_eq!(*ret, GradualType::Dynamic);
            }
            _ => panic!("Expected GFunc"),
        }
        match func_ev.target() {
            GradualType::GFunc(params, ret) => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0], bool_ty);
                assert_eq!(*ret, int_ty);
            }
            _ => panic!("Expected GFunc"),
        }
    }

    #[test]
    fn test_evidence_invert() {
        let bool_ty = GradualType::ground(BrrrType::BOOL);

        let refl = Evidence::refl(bool_ty.clone());
        assert_eq!(refl.invert(), refl);

        let dyn_l = Evidence::dyn_left(bool_ty.clone());
        let inverted = dyn_l.invert();
        assert!(matches!(inverted, Evidence::DynR(_)));
        assert_eq!(inverted.source(), bool_ty);
        assert_eq!(inverted.target(), GradualType::Dynamic);

        let dyn_r = Evidence::dyn_right(bool_ty.clone());
        let inverted = dyn_r.invert();
        assert!(matches!(inverted, Evidence::DynL(_)));
        assert_eq!(inverted.source(), GradualType::Dynamic);
        assert_eq!(inverted.target(), bool_ty);

        assert_eq!(dyn_l.invert().invert(), dyn_l);
        assert_eq!(dyn_r.invert().invert(), dyn_r);
    }

    #[test]
    fn test_compose_identity() {
        let bool_ty = GradualType::ground(BrrrType::BOOL);
        let int_ty = GradualType::ground(BrrrType::Numeric(crate::types::NumericType::Int(crate::types::IntType::I64)));

        let refl = Evidence::refl(bool_ty.clone());
        let dyn_l = Evidence::dyn_left(int_ty.clone());

        match compose_evidence(&refl, &dyn_l) {
            EvidenceResult::Ok(ev) => assert_eq!(ev, dyn_l),
            _ => panic!("Expected Ok"),
        }

        match compose_evidence(&dyn_l, &refl) {
            EvidenceResult::Ok(ev) => assert_eq!(ev, dyn_l),
            _ => panic!("Expected Ok"),
        }
    }

    #[test]
    fn test_compose_dyn_success() {
        let bool_ty = GradualType::ground(BrrrType::BOOL);

        let dyn_l = Evidence::dyn_left(bool_ty.clone());
        let dyn_r = Evidence::dyn_right(bool_ty.clone());

        match compose_evidence(&dyn_l, &dyn_r) {
            EvidenceResult::Ok(Evidence::Refl(g)) => assert_eq!(g, bool_ty),
            _ => panic!("Expected Ok(Refl)"),
        }

        match compose_evidence(&dyn_r, &dyn_l) {
            EvidenceResult::Ok(Evidence::Refl(g)) => assert_eq!(g, bool_ty),
            _ => panic!("Expected Ok(Refl)"),
        }
    }

    #[test]
    fn test_compose_dyn_fail() {
        let bool_ty = GradualType::ground(BrrrType::BOOL);
        let int_ty = GradualType::ground(BrrrType::Numeric(crate::types::NumericType::Int(crate::types::IntType::I64)));

        let dyn_l = Evidence::dyn_left(bool_ty.clone());
        let dyn_r = Evidence::dyn_right(int_ty.clone());

        match compose_evidence(&dyn_l, &dyn_r) {
            EvidenceResult::Fail { from, to } => {
                assert_eq!(from, bool_ty);
                assert_eq!(to, int_ty);
            }
            _ => panic!("Expected Fail"),
        }
    }

    #[test]
    fn test_compose_dyn_chain() {
        let bool_ty = GradualType::ground(BrrrType::BOOL);

        let dyn_l1 = Evidence::dyn_left(bool_ty.clone());
        let dyn_l2 = Evidence::dyn_left(bool_ty.clone());
        match compose_evidence(&dyn_l1, &dyn_l2) {
            EvidenceResult::Ok(Evidence::DynL(g)) => assert_eq!(g, bool_ty),
            _ => panic!("Expected Ok(DynL)"),
        }

        let dyn_r1 = Evidence::dyn_right(bool_ty.clone());
        let dyn_r2 = Evidence::dyn_right(bool_ty.clone());
        match compose_evidence(&dyn_r1, &dyn_r2) {
            EvidenceResult::Ok(Evidence::DynR(g)) => assert_eq!(g, bool_ty),
            _ => panic!("Expected Ok(DynR)"),
        }
    }

    #[test]
    fn test_compose_func() {
        let bool_ty = GradualType::ground(BrrrType::BOOL);
        let int_ty = GradualType::ground(BrrrType::Numeric(crate::types::NumericType::Int(crate::types::IntType::I64)));

        let ev1 = Evidence::func(
            vec![Evidence::refl(bool_ty.clone())],
            Evidence::refl(int_ty.clone()),
        );
        let ev2 = Evidence::func(
            vec![Evidence::refl(bool_ty.clone())],
            Evidence::refl(int_ty.clone()),
        );

        match compose_evidence(&ev1, &ev2) {
            EvidenceResult::Ok(Evidence::Func(args, ret)) => {
                assert_eq!(args.len(), 1);
                assert!(matches!(&args[0], Evidence::Refl(_)));
                assert!(matches!(ret.as_ref(), Evidence::Refl(_)));
            }
            other => panic!("Expected Ok(Func), got {:?}", other),
        }
    }

    #[test]
    fn test_evidence_result_helpers() {
        let bool_ty = GradualType::ground(BrrrType::BOOL);
        let int_ty = GradualType::ground(BrrrType::Numeric(crate::types::NumericType::Int(crate::types::IntType::I64)));

        let ok = EvidenceResult::Ok(Evidence::refl(bool_ty.clone()));
        assert!(ok.is_ok());
        assert!(!ok.is_fail());
        assert!(ok.clone().ok().is_some());
        assert!(ok.fail().is_none());

        let fail = EvidenceResult::Fail {
            from: bool_ty.clone(),
            to: int_ty.clone(),
        };
        assert!(!fail.is_ok());
        assert!(fail.is_fail());
        assert!(fail.clone().ok().is_none());
        let (from, to) = fail.fail().unwrap();
        assert_eq!(from, bool_ty);
        assert_eq!(to, int_ty);
    }
}
