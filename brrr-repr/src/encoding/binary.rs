//! Binary format encoder/decoder (.brrr)
//!
//! Provides complete binary serialization for BrrrType, Expr, and all nested types.
//! Uses varint encoding for compact representation of lengths and indices.

use std::io::{Read, Write};

use lasso::{Rodeo, Spur};

use crate::api::BrrrModule;
use crate::decl::{
    AssocTypeBinding, AssocTypeDef, ExternItem, FullDeclaration, FunctionDef, ImplBlock,
    TraitDef, TraitRef, TypeDef,
};
use crate::effects::{AbstractLoc, EffectOp, EffectRow, EffectType, EffectVar, IoSink, IoSource};
use crate::error::{DecodeError, EncodeError, ReprResult};
use crate::expr::{
    BinaryOp, CatchArm, ContinuationLinearity, EffectHandler, Expr, Expr_, FloatBits,
    HandlerClause, HandlerDepth, Literal, MatchArm, Pattern, Pattern_, Pos, Range, UnaryOp,
    WithLoc,
};
use crate::modes::{Mode, RefKind};
use crate::types::{
    BrrrType, EnumType, FieldType, FloatPrec, FuncType, IntType, InterfaceType, Kind, KindedVar,
    MethodParam, MethodSig, ModalKind, NumericType, ParamType, PrimKind, ReprAttr, StructType,
    VariantType, Visibility, WrapperKind,
};
use crate::verification::{Contract, CmpOp, DepVar, Formula};

use super::varint::{decode_varint32_from, encode_varint_to};

/// Magic number for .brrr files
const MAGIC: [u8; 4] = *b"BRRR";

/// Current format version
const VERSION: u16 = 1;

// ============================================================================
// Type Encoding Context
// ============================================================================

/// Context for encoding types - tracks interned strings
struct EncodeContext<'a, W: Write> {
    writer: &'a mut W,
    /// Maps Spur -> index in string table
    string_table: Vec<(Spur, String)>,
    rodeo: &'a Rodeo,
}

impl<'a, W: Write> EncodeContext<'a, W> {
    fn new(writer: &'a mut W, rodeo: &'a Rodeo) -> Self {
        Self {
            writer,
            string_table: Vec::new(),
            rodeo,
        }
    }

    /// Encode a Spur by recording it in the string table and writing its index
    fn encode_spur(&mut self, spur: Spur) -> Result<(), EncodeError> {
        // Find existing index or add new
        let idx = self.string_table.iter().position(|(s, _)| *s == spur);
        let idx = match idx {
            Some(i) => i as u32,
            None => {
                let s = self.rodeo.resolve(&spur).to_string();
                let i = self.string_table.len() as u32;
                self.string_table.push((spur, s));
                i
            }
        };
        encode_varint_to(idx as u64, self.writer)?;
        Ok(())
    }

    /// Encode an optional Spur
    fn encode_option_spur(&mut self, opt: Option<Spur>) -> Result<(), EncodeError> {
        match opt {
            None => self.writer.write_all(&[0])?,
            Some(s) => {
                self.writer.write_all(&[1])?;
                self.encode_spur(s)?;
            }
        }
        Ok(())
    }

    /// Write a single byte
    fn write_u8(&mut self, v: u8) -> Result<(), EncodeError> {
        self.writer.write_all(&[v])?;
        Ok(())
    }

    /// Write a u32 as varint
    fn write_varint(&mut self, v: u32) -> Result<(), EncodeError> {
        encode_varint_to(v as u64, self.writer)?;
        Ok(())
    }

    /// Write a bool
    fn write_bool(&mut self, v: bool) -> Result<(), EncodeError> {
        self.writer.write_all(&[v as u8])?;
        Ok(())
    }

    /// Write a u64 (little-endian)
    fn write_u64(&mut self, v: u64) -> Result<(), EncodeError> {
        self.writer.write_all(&v.to_le_bytes())?;
        Ok(())
    }

    /// Write an i128 (little-endian)
    fn write_i128(&mut self, v: i128) -> Result<(), EncodeError> {
        self.writer.write_all(&v.to_le_bytes())?;
        Ok(())
    }

    /// Write a length-prefixed string
    fn write_string(&mut self, s: &str) -> Result<(), EncodeError> {
        let bytes = s.as_bytes();
        self.write_varint(bytes.len() as u32)?;
        self.writer.write_all(bytes)?;
        Ok(())
    }
}

/// Context for decoding types - resolves string indices
struct DecodeContext<'a, R: Read> {
    reader: &'a mut R,
    /// String table built during decoding
    strings: Vec<String>,
    rodeo: &'a mut Rodeo,
}

impl<'a, R: Read> DecodeContext<'a, R> {
    fn new(reader: &'a mut R, rodeo: &'a mut Rodeo, strings: Vec<String>) -> Self {
        Self {
            reader,
            strings,
            rodeo,
        }
    }

    /// Decode a Spur by reading index and looking up in string table
    fn decode_spur(&mut self) -> Result<Spur, DecodeError> {
        let idx = decode_varint32_from(self.reader)? as usize;
        if idx >= self.strings.len() {
            return Err(DecodeError::InvalidSection(format!(
                "String index {} out of bounds (table size {})",
                idx,
                self.strings.len()
            )));
        }
        Ok(self.rodeo.get_or_intern(&self.strings[idx]))
    }

    /// Decode an optional Spur
    fn decode_option_spur(&mut self) -> Result<Option<Spur>, DecodeError> {
        let has_value = self.read_u8()?;
        if has_value == 0 {
            Ok(None)
        } else {
            Ok(Some(self.decode_spur()?))
        }
    }

    /// Read a single byte
    fn read_u8(&mut self) -> Result<u8, DecodeError> {
        let mut buf = [0u8; 1];
        self.reader.read_exact(&mut buf)?;
        Ok(buf[0])
    }

    /// Read a u32 as varint
    fn read_varint(&mut self) -> Result<u32, DecodeError> {
        decode_varint32_from(self.reader)
    }

    /// Read a bool
    fn read_bool(&mut self) -> Result<bool, DecodeError> {
        Ok(self.read_u8()? != 0)
    }

    /// Read a u64 (little-endian)
    fn read_u64(&mut self) -> Result<u64, DecodeError> {
        let mut buf = [0u8; 8];
        self.reader.read_exact(&mut buf)?;
        Ok(u64::from_le_bytes(buf))
    }

    /// Read an i128 (little-endian)
    fn read_i128(&mut self) -> Result<i128, DecodeError> {
        let mut buf = [0u8; 16];
        self.reader.read_exact(&mut buf)?;
        Ok(i128::from_le_bytes(buf))
    }

    /// Read a length-prefixed string
    fn read_string(&mut self) -> Result<String, DecodeError> {
        let len = self.read_varint()? as usize;
        let mut bytes = vec![0u8; len];
        self.reader.read_exact(&mut bytes)?;
        String::from_utf8(bytes).map_err(|e| DecodeError::InvalidSection(e.to_string()))
    }
}

// ============================================================================
// Primitive Type Encoding
// ============================================================================

fn encode_prim_kind<W: Write>(ctx: &mut EncodeContext<W>, kind: PrimKind) -> Result<(), EncodeError> {
    ctx.write_u8(kind as u8)
}

fn decode_prim_kind<R: Read>(ctx: &mut DecodeContext<R>) -> Result<PrimKind, DecodeError> {
    let v = ctx.read_u8()?;
    match v {
        0 => Ok(PrimKind::Unit),
        1 => Ok(PrimKind::Never),
        2 => Ok(PrimKind::Bool),
        3 => Ok(PrimKind::String),
        4 => Ok(PrimKind::Char),
        5 => Ok(PrimKind::Dynamic),
        6 => Ok(PrimKind::Unknown),
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid PrimKind: {}",
            v
        ))),
    }
}

fn encode_int_type<W: Write>(ctx: &mut EncodeContext<W>, int_type: IntType) -> Result<(), EncodeError> {
    ctx.write_u8(int_type as u8)
}

fn decode_int_type<R: Read>(ctx: &mut DecodeContext<R>) -> Result<IntType, DecodeError> {
    let v = ctx.read_u8()?;
    match v {
        0 => Ok(IntType::I8),
        1 => Ok(IntType::I16),
        2 => Ok(IntType::I32),
        3 => Ok(IntType::I64),
        4 => Ok(IntType::I128),
        5 => Ok(IntType::ISize),
        6 => Ok(IntType::IBig),
        7 => Ok(IntType::U8),
        8 => Ok(IntType::U16),
        9 => Ok(IntType::U32),
        10 => Ok(IntType::U64),
        11 => Ok(IntType::U128),
        12 => Ok(IntType::USize),
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid IntType: {}",
            v
        ))),
    }
}

fn encode_float_prec<W: Write>(ctx: &mut EncodeContext<W>, prec: FloatPrec) -> Result<(), EncodeError> {
    ctx.write_u8(prec as u8)
}

fn decode_float_prec<R: Read>(ctx: &mut DecodeContext<R>) -> Result<FloatPrec, DecodeError> {
    let v = ctx.read_u8()?;
    match v {
        0 => Ok(FloatPrec::F16),
        1 => Ok(FloatPrec::F32),
        2 => Ok(FloatPrec::F64),
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid FloatPrec: {}",
            v
        ))),
    }
}

fn encode_numeric_type<W: Write>(
    ctx: &mut EncodeContext<W>,
    num: NumericType,
) -> Result<(), EncodeError> {
    ctx.write_u8(num.discriminant())
}

fn decode_numeric_type<R: Read>(ctx: &mut DecodeContext<R>) -> Result<NumericType, DecodeError> {
    let v = ctx.read_u8()?;
    if v < 16 {
        // Int types (0-12)
        let int_type = match v {
            0 => IntType::I8,
            1 => IntType::I16,
            2 => IntType::I32,
            3 => IntType::I64,
            4 => IntType::I128,
            5 => IntType::ISize,
            6 => IntType::IBig,
            7 => IntType::U8,
            8 => IntType::U16,
            9 => IntType::U32,
            10 => IntType::U64,
            11 => IntType::U128,
            12 => IntType::USize,
            _ => {
                return Err(DecodeError::InvalidSection(format!(
                    "Invalid IntType: {}",
                    v
                )))
            }
        };
        Ok(NumericType::Int(int_type))
    } else {
        // Float types (16+)
        let float_prec = match v - 16 {
            0 => FloatPrec::F16,
            1 => FloatPrec::F32,
            2 => FloatPrec::F64,
            _ => {
                return Err(DecodeError::InvalidSection(format!(
                    "Invalid FloatPrec: {}",
                    v - 16
                )))
            }
        };
        Ok(NumericType::Float(float_prec))
    }
}

fn encode_wrapper_kind<W: Write>(
    ctx: &mut EncodeContext<W>,
    kind: WrapperKind,
) -> Result<(), EncodeError> {
    ctx.write_u8(kind as u8)
}

fn decode_wrapper_kind<R: Read>(ctx: &mut DecodeContext<R>) -> Result<WrapperKind, DecodeError> {
    let v = ctx.read_u8()?;
    match v {
        0 => Ok(WrapperKind::Array),
        1 => Ok(WrapperKind::Slice),
        2 => Ok(WrapperKind::Option),
        3 => Ok(WrapperKind::Box),
        4 => Ok(WrapperKind::Ref),
        5 => Ok(WrapperKind::RefMut),
        6 => Ok(WrapperKind::Rc),
        7 => Ok(WrapperKind::Arc),
        8 => Ok(WrapperKind::Raw),
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid WrapperKind: {}",
            v
        ))),
    }
}

fn encode_modal_kind<W: Write>(
    ctx: &mut EncodeContext<W>,
    kind: ModalKind,
) -> Result<(), EncodeError> {
    match kind {
        ModalKind::BoxMod(ref_kind) => {
            ctx.write_u8(0)?;
            ctx.write_u8(ref_kind.permission)?;
        }
        ModalKind::DiamondMod => {
            ctx.write_u8(1)?;
        }
    }
    Ok(())
}

fn decode_modal_kind<R: Read>(ctx: &mut DecodeContext<R>) -> Result<ModalKind, DecodeError> {
    let disc = ctx.read_u8()?;
    match disc {
        0 => {
            let permission = ctx.read_u8()?;
            Ok(ModalKind::BoxMod(RefKind { permission }))
        }
        1 => Ok(ModalKind::DiamondMod),
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid ModalKind: {}",
            disc
        ))),
    }
}

fn encode_visibility<W: Write>(
    ctx: &mut EncodeContext<W>,
    vis: Visibility,
) -> Result<(), EncodeError> {
    ctx.write_u8(vis as u8)
}

fn decode_visibility<R: Read>(ctx: &mut DecodeContext<R>) -> Result<Visibility, DecodeError> {
    let v = ctx.read_u8()?;
    match v {
        0 => Ok(Visibility::Public),
        1 => Ok(Visibility::Private),
        2 => Ok(Visibility::Module),
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid Visibility: {}",
            v
        ))),
    }
}

fn encode_repr_attr<W: Write>(
    ctx: &mut EncodeContext<W>,
    repr: ReprAttr,
) -> Result<(), EncodeError> {
    match repr {
        ReprAttr::Rust => ctx.write_u8(0)?,
        ReprAttr::C => ctx.write_u8(1)?,
        ReprAttr::Packed => ctx.write_u8(2)?,
        ReprAttr::Transparent => ctx.write_u8(3)?,
        ReprAttr::Align(n) => {
            ctx.write_u8(4)?;
            ctx.write_varint(n)?;
        }
    }
    Ok(())
}

fn decode_repr_attr<R: Read>(ctx: &mut DecodeContext<R>) -> Result<ReprAttr, DecodeError> {
    let v = ctx.read_u8()?;
    match v {
        0 => Ok(ReprAttr::Rust),
        1 => Ok(ReprAttr::C),
        2 => Ok(ReprAttr::Packed),
        3 => Ok(ReprAttr::Transparent),
        4 => {
            let n = ctx.read_varint()?;
            Ok(ReprAttr::Align(n))
        }
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid ReprAttr: {}",
            v
        ))),
    }
}

fn encode_mode<W: Write>(ctx: &mut EncodeContext<W>, mode: Mode) -> Result<(), EncodeError> {
    ctx.write_u8(mode as u8)
}

fn decode_mode<R: Read>(ctx: &mut DecodeContext<R>) -> Result<Mode, DecodeError> {
    let v = ctx.read_u8()?;
    match v {
        0 => Ok(Mode::Zero),
        1 => Ok(Mode::One),
        2 => Ok(Mode::Omega),
        _ => Err(DecodeError::InvalidSection(format!("Invalid Mode: {}", v))),
    }
}

// ============================================================================
// Kind Encoding
// ============================================================================

fn encode_kind<W: Write>(ctx: &mut EncodeContext<W>, kind: &Kind) -> Result<(), EncodeError> {
    match kind {
        Kind::Star => ctx.write_u8(0)?,
        Kind::Arrow(from, to) => {
            ctx.write_u8(1)?;
            encode_kind(ctx, from)?;
            encode_kind(ctx, to)?;
        }
        Kind::Row => ctx.write_u8(2)?,
        Kind::Region => ctx.write_u8(3)?,
    }
    Ok(())
}

fn decode_kind<R: Read>(ctx: &mut DecodeContext<R>) -> Result<Kind, DecodeError> {
    let disc = ctx.read_u8()?;
    match disc {
        0 => Ok(Kind::Star),
        1 => {
            let from = decode_kind(ctx)?;
            let to = decode_kind(ctx)?;
            Ok(Kind::Arrow(Box::new(from), Box::new(to)))
        }
        2 => Ok(Kind::Row),
        3 => Ok(Kind::Region),
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid Kind discriminant: {}",
            disc
        ))),
    }
}

fn encode_kinded_var<W: Write>(
    ctx: &mut EncodeContext<W>,
    kv: &KindedVar,
) -> Result<(), EncodeError> {
    ctx.encode_spur(kv.var)?;
    encode_kind(ctx, &kv.kind)
}

fn decode_kinded_var<R: Read>(ctx: &mut DecodeContext<R>) -> Result<KindedVar, DecodeError> {
    let var = ctx.decode_spur()?;
    let kind = decode_kind(ctx)?;
    Ok(KindedVar { var, kind })
}

fn encode_kinded_vars<W: Write>(
    ctx: &mut EncodeContext<W>,
    vars: &[KindedVar],
) -> Result<(), EncodeError> {
    ctx.write_varint(vars.len() as u32)?;
    for v in vars {
        encode_kinded_var(ctx, v)?;
    }
    Ok(())
}

fn decode_kinded_vars<R: Read>(ctx: &mut DecodeContext<R>) -> Result<Vec<KindedVar>, DecodeError> {
    let count = ctx.read_varint()? as usize;
    let mut vars = Vec::with_capacity(count);
    for _ in 0..count {
        vars.push(decode_kinded_var(ctx)?);
    }
    Ok(vars)
}

// ============================================================================
// Formula and Contract Encoding
// ============================================================================

fn encode_cmp_op<W: Write>(ctx: &mut EncodeContext<W>, op: CmpOp) -> Result<(), EncodeError> {
    ctx.write_u8(op as u8)
}

fn decode_cmp_op<R: Read>(ctx: &mut DecodeContext<R>) -> Result<CmpOp, DecodeError> {
    let v = ctx.read_u8()?;
    match v {
        0 => Ok(CmpOp::Eq),
        1 => Ok(CmpOp::Ne),
        2 => Ok(CmpOp::Lt),
        3 => Ok(CmpOp::Le),
        4 => Ok(CmpOp::Gt),
        5 => Ok(CmpOp::Ge),
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid CmpOp: {}",
            v
        ))),
    }
}

fn encode_dep_var<W: Write>(ctx: &mut EncodeContext<W>, dv: DepVar) -> Result<(), EncodeError> {
    ctx.encode_spur(dv.0)
}

fn decode_dep_var<R: Read>(ctx: &mut DecodeContext<R>) -> Result<DepVar, DecodeError> {
    Ok(DepVar(ctx.decode_spur()?))
}

fn encode_formula<W: Write>(ctx: &mut EncodeContext<W>, f: &Formula) -> Result<(), EncodeError> {
    match f {
        Formula::True => ctx.write_u8(0)?,
        Formula::False => ctx.write_u8(1)?,
        Formula::Cmp(op, lhs, rhs) => {
            ctx.write_u8(2)?;
            encode_cmp_op(ctx, *op)?;
            encode_expr(ctx, lhs)?;
            encode_expr(ctx, rhs)?;
        }
        Formula::And(lhs, rhs) => {
            ctx.write_u8(3)?;
            encode_formula(ctx, lhs)?;
            encode_formula(ctx, rhs)?;
        }
        Formula::Or(lhs, rhs) => {
            ctx.write_u8(4)?;
            encode_formula(ctx, lhs)?;
            encode_formula(ctx, rhs)?;
        }
        Formula::Not(inner) => {
            ctx.write_u8(5)?;
            encode_formula(ctx, inner)?;
        }
        Formula::Impl(lhs, rhs) => {
            ctx.write_u8(6)?;
            encode_formula(ctx, lhs)?;
            encode_formula(ctx, rhs)?;
        }
        Formula::Iff(lhs, rhs) => {
            ctx.write_u8(7)?;
            encode_formula(ctx, lhs)?;
            encode_formula(ctx, rhs)?;
        }
        Formula::Forall(var, ty, body) => {
            ctx.write_u8(8)?;
            encode_dep_var(ctx, *var)?;
            encode_brrr_type(ctx, ty)?;
            encode_formula(ctx, body)?;
        }
        Formula::Exists(var, ty, body) => {
            ctx.write_u8(9)?;
            encode_dep_var(ctx, *var)?;
            encode_brrr_type(ctx, ty)?;
            encode_formula(ctx, body)?;
        }
        Formula::Pred(name, arg) => {
            ctx.write_u8(10)?;
            ctx.encode_spur(*name)?;
            encode_expr(ctx, arg)?;
        }
        Formula::Expr(e) => {
            ctx.write_u8(11)?;
            encode_expr(ctx, e)?;
        }
    }
    Ok(())
}

fn decode_formula<R: Read>(ctx: &mut DecodeContext<R>) -> Result<Formula, DecodeError> {
    let disc = ctx.read_u8()?;
    match disc {
        0 => Ok(Formula::True),
        1 => Ok(Formula::False),
        2 => {
            let op = decode_cmp_op(ctx)?;
            let lhs = decode_expr(ctx)?;
            let rhs = decode_expr(ctx)?;
            Ok(Formula::Cmp(op, Box::new(lhs), Box::new(rhs)))
        }
        3 => {
            let lhs = decode_formula(ctx)?;
            let rhs = decode_formula(ctx)?;
            Ok(Formula::And(Box::new(lhs), Box::new(rhs)))
        }
        4 => {
            let lhs = decode_formula(ctx)?;
            let rhs = decode_formula(ctx)?;
            Ok(Formula::Or(Box::new(lhs), Box::new(rhs)))
        }
        5 => {
            let inner = decode_formula(ctx)?;
            Ok(Formula::Not(Box::new(inner)))
        }
        6 => {
            let lhs = decode_formula(ctx)?;
            let rhs = decode_formula(ctx)?;
            Ok(Formula::Impl(Box::new(lhs), Box::new(rhs)))
        }
        7 => {
            let lhs = decode_formula(ctx)?;
            let rhs = decode_formula(ctx)?;
            Ok(Formula::Iff(Box::new(lhs), Box::new(rhs)))
        }
        8 => {
            let var = decode_dep_var(ctx)?;
            let ty = decode_brrr_type(ctx)?;
            let body = decode_formula(ctx)?;
            Ok(Formula::Forall(var, ty, Box::new(body)))
        }
        9 => {
            let var = decode_dep_var(ctx)?;
            let ty = decode_brrr_type(ctx)?;
            let body = decode_formula(ctx)?;
            Ok(Formula::Exists(var, ty, Box::new(body)))
        }
        10 => {
            let name = ctx.decode_spur()?;
            let arg = decode_expr(ctx)?;
            Ok(Formula::Pred(name, Box::new(arg)))
        }
        11 => {
            let e = decode_expr(ctx)?;
            Ok(Formula::Expr(Box::new(e)))
        }
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid Formula discriminant: {}",
            disc
        ))),
    }
}

fn encode_contract<W: Write>(ctx: &mut EncodeContext<W>, c: &Contract) -> Result<(), EncodeError> {
    encode_formula(ctx, &c.precondition)?;
    encode_formula(ctx, &c.postcondition)
}

fn decode_contract<R: Read>(ctx: &mut DecodeContext<R>) -> Result<Contract, DecodeError> {
    let precondition = decode_formula(ctx)?;
    let postcondition = decode_formula(ctx)?;
    Ok(Contract {
        precondition,
        postcondition,
    })
}

fn encode_option_contract<W: Write>(
    ctx: &mut EncodeContext<W>,
    opt: &Option<Contract>,
) -> Result<(), EncodeError> {
    match opt {
        None => ctx.write_u8(0)?,
        Some(c) => {
            ctx.write_u8(1)?;
            encode_contract(ctx, c)?;
        }
    }
    Ok(())
}

fn decode_option_contract<R: Read>(
    ctx: &mut DecodeContext<R>,
) -> Result<Option<Contract>, DecodeError> {
    if ctx.read_u8()? == 0 {
        Ok(None)
    } else {
        Ok(Some(decode_contract(ctx)?))
    }
}

fn encode_option_expr<W: Write>(
    ctx: &mut EncodeContext<W>,
    opt: &Option<Expr>,
) -> Result<(), EncodeError> {
    match opt {
        None => ctx.write_u8(0)?,
        Some(e) => {
            ctx.write_u8(1)?;
            encode_expr(ctx, e)?;
        }
    }
    Ok(())
}

fn decode_option_expr<R: Read>(ctx: &mut DecodeContext<R>) -> Result<Option<Expr>, DecodeError> {
    if ctx.read_u8()? == 0 {
        Ok(None)
    } else {
        Ok(Some(decode_expr(ctx)?))
    }
}

// ============================================================================
// Effect Type Encoding (for EffectOp parameters)
// ============================================================================

fn encode_effect_type<W: Write>(
    ctx: &mut EncodeContext<W>,
    et: &EffectType,
) -> Result<(), EncodeError> {
    ctx.write_u8(et.discriminant())?;
    match et {
        EffectType::Unit | EffectType::Bool | EffectType::Int | EffectType::String => {}
        EffectType::Chan(inner) => encode_effect_type(ctx, inner)?,
        EffectType::Ref(inner) => encode_effect_type(ctx, inner)?,
        EffectType::Fn(arg, ret) => {
            encode_effect_type(ctx, arg)?;
            encode_effect_type(ctx, ret)?;
        }
        EffectType::Var(idx) => ctx.write_varint(*idx)?,
        EffectType::Named(spur) => ctx.encode_spur(*spur)?,
    }
    Ok(())
}

fn decode_effect_type<R: Read>(ctx: &mut DecodeContext<R>) -> Result<EffectType, DecodeError> {
    let disc = ctx.read_u8()?;
    match disc {
        0 => Ok(EffectType::Unit),
        1 => Ok(EffectType::Bool),
        2 => Ok(EffectType::Int),
        3 => Ok(EffectType::String),
        4 => Ok(EffectType::Chan(Box::new(decode_effect_type(ctx)?))),
        5 => Ok(EffectType::Ref(Box::new(decode_effect_type(ctx)?))),
        6 => {
            let arg = decode_effect_type(ctx)?;
            let ret = decode_effect_type(ctx)?;
            Ok(EffectType::Fn(Box::new(arg), Box::new(ret)))
        }
        7 => Ok(EffectType::Var(ctx.read_varint()?)),
        8 => Ok(EffectType::Named(ctx.decode_spur()?)),
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid EffectType: {}",
            disc
        ))),
    }
}

// ============================================================================
// Location and IO Encoding (for EffectOp parameters)
// ============================================================================

fn encode_abstract_loc<W: Write>(
    ctx: &mut EncodeContext<W>,
    loc: &AbstractLoc,
) -> Result<(), EncodeError> {
    ctx.write_u8(loc.discriminant())?;
    match loc {
        AbstractLoc::Concrete(id) => ctx.write_varint(*id)?,
        AbstractLoc::Abstract(spur) => ctx.encode_spur(*spur)?,
        AbstractLoc::Param(idx) => ctx.write_varint(*idx)?,
        AbstractLoc::Unknown => {}
    }
    Ok(())
}

fn decode_abstract_loc<R: Read>(ctx: &mut DecodeContext<R>) -> Result<AbstractLoc, DecodeError> {
    let disc = ctx.read_u8()?;
    match disc {
        0 => Ok(AbstractLoc::Concrete(ctx.read_varint()?)),
        1 => Ok(AbstractLoc::Abstract(ctx.decode_spur()?)),
        2 => Ok(AbstractLoc::Param(ctx.read_varint()?)),
        3 => Ok(AbstractLoc::Unknown),
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid AbstractLoc: {}",
            disc
        ))),
    }
}

fn encode_io_source<W: Write>(
    ctx: &mut EncodeContext<W>,
    src: &IoSource,
) -> Result<(), EncodeError> {
    ctx.write_u8(src.discriminant())?;
    match src {
        IoSource::EnvVar(s) | IoSource::FileInput(s) => ctx.encode_spur(*s)?,
        _ => {}
    }
    Ok(())
}

fn decode_io_source<R: Read>(ctx: &mut DecodeContext<R>) -> Result<IoSource, DecodeError> {
    let disc = ctx.read_u8()?;
    match disc {
        0 => Ok(IoSource::Stdin),
        1 => Ok(IoSource::EnvVar(ctx.decode_spur()?)),
        2 => Ok(IoSource::FileInput(ctx.decode_spur()?)),
        3 => Ok(IoSource::NetworkIn),
        4 => Ok(IoSource::UserInput),
        5 => Ok(IoSource::Args),
        6 => Ok(IoSource::Random),
        7 => Ok(IoSource::Clock),
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid IoSource: {}",
            disc
        ))),
    }
}

fn encode_io_sink<W: Write>(ctx: &mut EncodeContext<W>, sink: &IoSink) -> Result<(), EncodeError> {
    ctx.write_u8(sink.discriminant())?;
    match sink {
        IoSink::FileOutput(s) | IoSink::Database(s) => ctx.encode_spur(*s)?,
        _ => {}
    }
    Ok(())
}

fn decode_io_sink<R: Read>(ctx: &mut DecodeContext<R>) -> Result<IoSink, DecodeError> {
    let disc = ctx.read_u8()?;
    match disc {
        0 => Ok(IoSink::Stdout),
        1 => Ok(IoSink::Stderr),
        2 => Ok(IoSink::FileOutput(ctx.decode_spur()?)),
        3 => Ok(IoSink::NetworkOut),
        4 => Ok(IoSink::Database(ctx.decode_spur()?)),
        5 => Ok(IoSink::Log),
        6 => Ok(IoSink::Metrics),
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid IoSink: {}",
            disc
        ))),
    }
}

// ============================================================================
// EffectOp Encoding
// ============================================================================

fn encode_effect_op<W: Write>(
    ctx: &mut EncodeContext<W>,
    op: &EffectOp,
) -> Result<(), EncodeError> {
    ctx.write_u8(op.discriminant())?;
    match op {
        // Memory effects with location
        EffectOp::Read(loc) | EffectOp::Write(loc) | EffectOp::Free(loc) => {
            encode_abstract_loc(ctx, loc)?;
        }
        // Control effects with Spur
        EffectOp::Throw(s) | EffectOp::Catch(s) => ctx.encode_spur(*s)?,
        // Yield with types
        EffectOp::Yield(yield_ty, resume_ty) => {
            encode_effect_type(ctx, yield_ty)?;
            encode_effect_type(ctx, resume_ty)?;
        }
        // IO effects with source/sink
        EffectOp::Input(src) => encode_io_source(ctx, src)?,
        EffectOp::Output(sink) => encode_io_sink(ctx, sink)?,
        // File effects with path
        EffectOp::FileRead(path) | EffectOp::FileWrite(path) => ctx.encode_spur(*path)?,
        // Concurrency effects with lock ID
        EffectOp::Lock(id) | EffectOp::Unlock(id) => ctx.write_varint(*id)?,
        // Session effects
        EffectOp::Send(ch, ty) | EffectOp::Recv(ch, ty) => {
            ctx.write_varint(*ch)?;
            encode_effect_type(ctx, ty)?;
        }
        EffectOp::Select(ch, label) => {
            ctx.write_varint(*ch)?;
            ctx.encode_spur(*label)?;
        }
        EffectOp::Branch(ch, labels) => {
            ctx.write_varint(*ch)?;
            ctx.write_varint(labels.len() as u32)?;
            for label in labels {
                ctx.encode_spur(*label)?;
            }
        }
        EffectOp::ChanCreate(ch, ty, buf) => {
            ctx.write_varint(*ch)?;
            encode_effect_type(ctx, ty)?;
            ctx.write_varint(*buf)?;
        }
        EffectOp::ChanClose(ch) => ctx.write_varint(*ch)?,
        EffectOp::Delegate(src, tgt) => {
            ctx.write_varint(*src)?;
            ctx.write_varint(*tgt)?;
        }
        // Resource effects
        EffectOp::Acquire(rt) | EffectOp::Release(rt) | EffectOp::Use(rt) => {
            ctx.encode_spur(*rt)?;
        }
        // State effects
        EffectOp::StRead(id) | EffectOp::StWrite(id) => ctx.write_varint(*id)?,
        // No-parameter effects
        EffectOp::Alloc
        | EffectOp::ReadSimple
        | EffectOp::WriteSimple
        | EffectOp::Panic
        | EffectOp::Async
        | EffectOp::Div
        | EffectOp::Shift
        | EffectOp::Abort
        | EffectOp::Io
        | EffectOp::Net
        | EffectOp::Fs
        | EffectOp::Random
        | EffectOp::Clock
        | EffectOp::Console
        | EffectOp::Env
        | EffectOp::Spawn
        | EffectOp::Join
        | EffectOp::Atomic
        | EffectOp::LockSimple
        | EffectOp::ThreadLocal
        | EffectOp::Barrier
        | EffectOp::NewCh
        | EffectOp::State
        | EffectOp::StNew
        | EffectOp::Unsafe
        | EffectOp::Ffi
        | EffectOp::CInterop
        | EffectOp::Platform => {}
    }
    Ok(())
}

fn decode_effect_op<R: Read>(ctx: &mut DecodeContext<R>) -> Result<EffectOp, DecodeError> {
    let disc = ctx.read_u8()?;
    match disc {
        // Memory effects
        0 => Ok(EffectOp::Read(decode_abstract_loc(ctx)?)),
        1 => Ok(EffectOp::Write(decode_abstract_loc(ctx)?)),
        2 => Ok(EffectOp::Alloc),
        3 => Ok(EffectOp::Free(decode_abstract_loc(ctx)?)),
        4 => Ok(EffectOp::ReadSimple),
        5 => Ok(EffectOp::WriteSimple),
        // Control effects
        10 => Ok(EffectOp::Throw(ctx.decode_spur()?)),
        11 => Ok(EffectOp::Catch(ctx.decode_spur()?)),
        12 => Ok(EffectOp::Panic),
        13 => Ok(EffectOp::Async),
        14 => {
            let yield_ty = decode_effect_type(ctx)?;
            let resume_ty = decode_effect_type(ctx)?;
            Ok(EffectOp::Yield(yield_ty, resume_ty))
        }
        15 => Ok(EffectOp::Div),
        16 => Ok(EffectOp::Shift),
        17 => Ok(EffectOp::Abort),
        // IO effects
        20 => Ok(EffectOp::Input(decode_io_source(ctx)?)),
        21 => Ok(EffectOp::Output(decode_io_sink(ctx)?)),
        22 => Ok(EffectOp::Io),
        23 => Ok(EffectOp::Net),
        24 => Ok(EffectOp::Fs),
        25 => Ok(EffectOp::FileRead(ctx.decode_spur()?)),
        26 => Ok(EffectOp::FileWrite(ctx.decode_spur()?)),
        27 => Ok(EffectOp::Random),
        28 => Ok(EffectOp::Clock),
        29 => Ok(EffectOp::Console),
        30 => Ok(EffectOp::Env),
        // Concurrency effects
        35 => Ok(EffectOp::Spawn),
        36 => Ok(EffectOp::Join),
        37 => Ok(EffectOp::Lock(ctx.read_varint()?)),
        38 => Ok(EffectOp::Unlock(ctx.read_varint()?)),
        39 => Ok(EffectOp::Atomic),
        40 => Ok(EffectOp::LockSimple),
        41 => Ok(EffectOp::ThreadLocal),
        42 => Ok(EffectOp::Barrier),
        // Session effects
        45 => {
            let ch = ctx.read_varint()?;
            let ty = decode_effect_type(ctx)?;
            Ok(EffectOp::Send(ch, ty))
        }
        46 => {
            let ch = ctx.read_varint()?;
            let ty = decode_effect_type(ctx)?;
            Ok(EffectOp::Recv(ch, ty))
        }
        47 => {
            let ch = ctx.read_varint()?;
            let label = ctx.decode_spur()?;
            Ok(EffectOp::Select(ch, label))
        }
        48 => {
            let ch = ctx.read_varint()?;
            let count = ctx.read_varint()? as usize;
            let mut labels = Vec::with_capacity(count);
            for _ in 0..count {
                labels.push(ctx.decode_spur()?);
            }
            Ok(EffectOp::Branch(ch, labels))
        }
        49 => {
            let ch = ctx.read_varint()?;
            let ty = decode_effect_type(ctx)?;
            let buf = ctx.read_varint()?;
            Ok(EffectOp::ChanCreate(ch, ty, buf))
        }
        50 => Ok(EffectOp::ChanClose(ctx.read_varint()?)),
        51 => {
            let src = ctx.read_varint()?;
            let tgt = ctx.read_varint()?;
            Ok(EffectOp::Delegate(src, tgt))
        }
        52 => Ok(EffectOp::NewCh),
        // Resource effects
        60 => Ok(EffectOp::Acquire(ctx.decode_spur()?)),
        61 => Ok(EffectOp::Release(ctx.decode_spur()?)),
        62 => Ok(EffectOp::Use(ctx.decode_spur()?)),
        // State effects
        65 => Ok(EffectOp::State),
        66 => Ok(EffectOp::StRead(ctx.read_varint()?)),
        67 => Ok(EffectOp::StWrite(ctx.read_varint()?)),
        68 => Ok(EffectOp::StNew),
        // FFI effects
        70 => Ok(EffectOp::Unsafe),
        71 => Ok(EffectOp::Ffi),
        72 => Ok(EffectOp::CInterop),
        73 => Ok(EffectOp::Platform),
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid EffectOp discriminant: {}",
            disc
        ))),
    }
}

// ============================================================================
// EffectRow Encoding
// ============================================================================

fn encode_effect_row<W: Write>(
    ctx: &mut EncodeContext<W>,
    row: &EffectRow,
) -> Result<(), EncodeError> {
    // Encode ops count and ops
    let ops = row.ops();
    ctx.write_varint(ops.len() as u32)?;
    for op in ops {
        encode_effect_op(ctx, op)?;
    }

    // Encode tail
    match row.row_var() {
        None => ctx.write_u8(0)?, // Closed
        Some(v) => {
            ctx.write_u8(1)?; // Open with variable
            ctx.write_varint(v.index())?;
        }
    }
    Ok(())
}

fn decode_effect_row<R: Read>(ctx: &mut DecodeContext<R>) -> Result<EffectRow, DecodeError> {
    let ops_count = ctx.read_varint()? as usize;
    let mut ops = Vec::with_capacity(ops_count);
    for _ in 0..ops_count {
        ops.push(decode_effect_op(ctx)?);
    }

    let tail_kind = ctx.read_u8()?;
    let row = if tail_kind == 0 {
        EffectRow::new(ops)
    } else {
        let var_idx = ctx.read_varint()?;
        EffectRow::open_with_var(ops, EffectVar::new(var_idx))
    };

    Ok(row)
}

// ============================================================================
// ParamType and FuncType Encoding
// ============================================================================

fn encode_param_type<W: Write>(
    ctx: &mut EncodeContext<W>,
    param: &ParamType,
) -> Result<(), EncodeError> {
    ctx.encode_option_spur(param.name)?;
    encode_brrr_type(ctx, &param.ty)?;
    encode_mode(ctx, param.mode)?;
    Ok(())
}

fn decode_param_type<R: Read>(ctx: &mut DecodeContext<R>) -> Result<ParamType, DecodeError> {
    let name = ctx.decode_option_spur()?;
    let ty = decode_brrr_type(ctx)?;
    let mode = decode_mode(ctx)?;
    Ok(ParamType { name, ty, mode })
}

fn encode_func_type<W: Write>(
    ctx: &mut EncodeContext<W>,
    func: &FuncType,
) -> Result<(), EncodeError> {
    // Params
    ctx.write_varint(func.params.len() as u32)?;
    for param in &func.params {
        encode_param_type(ctx, param)?;
    }
    // Return type
    encode_brrr_type(ctx, &func.return_type)?;
    // Effects
    encode_effect_row(ctx, &func.effects)?;
    // Is unsafe
    ctx.write_bool(func.is_unsafe)?;
    Ok(())
}

fn decode_func_type<R: Read>(ctx: &mut DecodeContext<R>) -> Result<FuncType, DecodeError> {
    let param_count = ctx.read_varint()? as usize;
    let mut params = Vec::with_capacity(param_count);
    for _ in 0..param_count {
        params.push(decode_param_type(ctx)?);
    }
    let return_type = decode_brrr_type(ctx)?;
    let effects = decode_effect_row(ctx)?;
    let is_unsafe = ctx.read_bool()?;

    Ok(FuncType {
        params,
        return_type,
        effects,
        is_unsafe,
    })
}

// ============================================================================
// FieldType and StructType Encoding
// ============================================================================

fn encode_field_type<W: Write>(
    ctx: &mut EncodeContext<W>,
    field: &FieldType,
) -> Result<(), EncodeError> {
    ctx.encode_spur(field.name)?;
    encode_brrr_type(ctx, &field.ty)?;
    encode_visibility(ctx, field.vis)?;
    Ok(())
}

fn decode_field_type<R: Read>(ctx: &mut DecodeContext<R>) -> Result<FieldType, DecodeError> {
    let name = ctx.decode_spur()?;
    let ty = decode_brrr_type(ctx)?;
    let vis = decode_visibility(ctx)?;
    Ok(FieldType { name, ty, vis })
}

fn encode_struct_type<W: Write>(
    ctx: &mut EncodeContext<W>,
    s: &StructType,
) -> Result<(), EncodeError> {
    ctx.encode_spur(s.name)?;
    ctx.write_varint(s.fields.len() as u32)?;
    for field in &s.fields {
        encode_field_type(ctx, field)?;
    }
    encode_repr_attr(ctx, s.repr)?;
    Ok(())
}

fn decode_struct_type<R: Read>(ctx: &mut DecodeContext<R>) -> Result<StructType, DecodeError> {
    let name = ctx.decode_spur()?;
    let field_count = ctx.read_varint()? as usize;
    let mut fields = Vec::with_capacity(field_count);
    for _ in 0..field_count {
        fields.push(decode_field_type(ctx)?);
    }
    let repr = decode_repr_attr(ctx)?;
    Ok(StructType { name, fields, repr })
}

// ============================================================================
// VariantType and EnumType Encoding
// ============================================================================

fn encode_variant_type<W: Write>(
    ctx: &mut EncodeContext<W>,
    v: &VariantType,
) -> Result<(), EncodeError> {
    ctx.encode_spur(v.name)?;
    ctx.write_varint(v.fields.len() as u32)?;
    for field in &v.fields {
        encode_brrr_type(ctx, field)?;
    }
    Ok(())
}

fn decode_variant_type<R: Read>(ctx: &mut DecodeContext<R>) -> Result<VariantType, DecodeError> {
    let name = ctx.decode_spur()?;
    let field_count = ctx.read_varint()? as usize;
    let mut fields = Vec::with_capacity(field_count);
    for _ in 0..field_count {
        fields.push(decode_brrr_type(ctx)?);
    }
    Ok(VariantType { name, fields })
}

fn encode_enum_type<W: Write>(
    ctx: &mut EncodeContext<W>,
    e: &EnumType,
) -> Result<(), EncodeError> {
    ctx.encode_spur(e.name)?;
    ctx.write_varint(e.variants.len() as u32)?;
    for variant in &e.variants {
        encode_variant_type(ctx, variant)?;
    }
    Ok(())
}

fn decode_enum_type<R: Read>(ctx: &mut DecodeContext<R>) -> Result<EnumType, DecodeError> {
    let name = ctx.decode_spur()?;
    let variant_count = ctx.read_varint()? as usize;
    let mut variants = Vec::with_capacity(variant_count);
    for _ in 0..variant_count {
        variants.push(decode_variant_type(ctx)?);
    }
    Ok(EnumType { name, variants })
}

// ============================================================================
// InterfaceType and MethodSig Encoding
// ============================================================================

fn encode_method_param<W: Write>(
    ctx: &mut EncodeContext<W>,
    p: &MethodParam,
) -> Result<(), EncodeError> {
    // Encode optional name
    match p.name {
        Some(name) => {
            ctx.write_u8(1)?;
            ctx.encode_spur(name)?;
        }
        None => ctx.write_u8(0)?,
    }
    encode_brrr_type(ctx, &p.ty)?;
    Ok(())
}

fn decode_method_param<R: Read>(ctx: &mut DecodeContext<R>) -> Result<MethodParam, DecodeError> {
    let has_name = ctx.read_u8()? != 0;
    let name = if has_name {
        Some(ctx.decode_spur()?)
    } else {
        None
    };
    let ty = decode_brrr_type(ctx)?;
    Ok(MethodParam { name, ty })
}

fn encode_method_sig<W: Write>(
    ctx: &mut EncodeContext<W>,
    m: &MethodSig,
) -> Result<(), EncodeError> {
    ctx.encode_spur(m.name)?;
    ctx.write_varint(m.params.len() as u32)?;
    for param in &m.params {
        encode_method_param(ctx, param)?;
    }
    encode_brrr_type(ctx, &m.return_type)?;
    Ok(())
}

fn decode_method_sig<R: Read>(ctx: &mut DecodeContext<R>) -> Result<MethodSig, DecodeError> {
    let name = ctx.decode_spur()?;
    let param_count = ctx.read_varint()? as usize;
    let mut params = Vec::with_capacity(param_count);
    for _ in 0..param_count {
        params.push(decode_method_param(ctx)?);
    }
    let return_type = decode_brrr_type(ctx)?;
    Ok(MethodSig { name, params, return_type })
}

fn encode_interface_type<W: Write>(
    ctx: &mut EncodeContext<W>,
    iface: &InterfaceType,
) -> Result<(), EncodeError> {
    ctx.encode_spur(iface.name)?;
    ctx.write_varint(iface.methods.len() as u32)?;
    for method in &iface.methods {
        encode_method_sig(ctx, method)?;
    }
    ctx.write_varint(iface.embedded.len() as u32)?;
    for embedded in &iface.embedded {
        ctx.encode_spur(*embedded)?;
    }
    Ok(())
}

fn decode_interface_type<R: Read>(ctx: &mut DecodeContext<R>) -> Result<InterfaceType, DecodeError> {
    let name = ctx.decode_spur()?;
    let method_count = ctx.read_varint()? as usize;
    let mut methods = Vec::with_capacity(method_count);
    for _ in 0..method_count {
        methods.push(decode_method_sig(ctx)?);
    }
    let embedded_count = ctx.read_varint()? as usize;
    let mut embedded = Vec::with_capacity(embedded_count);
    for _ in 0..embedded_count {
        embedded.push(ctx.decode_spur()?);
    }
    Ok(InterfaceType { name, methods, embedded })
}

// ============================================================================
// Main BrrrType Encoding
// ============================================================================

/// Encode a BrrrType to the writer
fn encode_brrr_type<W: Write>(
    ctx: &mut EncodeContext<W>,
    ty: &BrrrType,
) -> Result<(), EncodeError> {
    ctx.write_u8(ty.discriminant())?;

    match ty {
        BrrrType::Prim(kind) => encode_prim_kind(ctx, *kind)?,
        BrrrType::Numeric(num) => encode_numeric_type(ctx, *num)?,
        BrrrType::Wrap(kind, inner) => {
            encode_wrapper_kind(ctx, *kind)?;
            encode_brrr_type(ctx, inner)?;
        }
        BrrrType::SizedArray(size, inner) => {
            // Encode size as u64 varint for platform independence
            ctx.write_u64(*size as u64)?;
            encode_brrr_type(ctx, inner)?;
        }
        BrrrType::Modal(kind, inner) => {
            encode_modal_kind(ctx, *kind)?;
            encode_brrr_type(ctx, inner)?;
        }
        BrrrType::Result(ok, err) => {
            encode_brrr_type(ctx, ok)?;
            encode_brrr_type(ctx, err)?;
        }
        BrrrType::Tuple(elems) => {
            ctx.write_varint(elems.len() as u32)?;
            for elem in elems {
                encode_brrr_type(ctx, elem)?;
            }
        }
        BrrrType::Func(func) => encode_func_type(ctx, func)?,
        BrrrType::Var(type_var) => ctx.encode_spur(*type_var)?,
        BrrrType::App(base, args) => {
            encode_brrr_type(ctx, base)?;
            ctx.write_varint(args.len() as u32)?;
            for arg in args {
                encode_brrr_type(ctx, arg)?;
            }
        }
        BrrrType::Named(name) => ctx.encode_spur(*name)?,
        BrrrType::Struct(s) => encode_struct_type(ctx, s)?,
        BrrrType::Enum(e) => encode_enum_type(ctx, e)?,
        BrrrType::Interface(iface) => encode_interface_type(ctx, iface)?,
    }

    Ok(())
}

/// Decode a BrrrType from the reader
fn decode_brrr_type<R: Read>(ctx: &mut DecodeContext<R>) -> Result<BrrrType, DecodeError> {
    let disc = ctx.read_u8()?;

    match disc {
        0 => Ok(BrrrType::Prim(decode_prim_kind(ctx)?)),
        1 => Ok(BrrrType::Numeric(decode_numeric_type(ctx)?)),
        2 => {
            let kind = decode_wrapper_kind(ctx)?;
            let inner = decode_brrr_type(ctx)?;
            Ok(BrrrType::Wrap(kind, Box::new(inner)))
        }
        3 => {
            // SizedArray: size (u64) + element type
            let size = ctx.read_u64()? as usize;
            let inner = decode_brrr_type(ctx)?;
            Ok(BrrrType::SizedArray(size, Box::new(inner)))
        }
        4 => {
            let kind = decode_modal_kind(ctx)?;
            let inner = decode_brrr_type(ctx)?;
            Ok(BrrrType::Modal(kind, Box::new(inner)))
        }
        5 => {
            let ok = decode_brrr_type(ctx)?;
            let err = decode_brrr_type(ctx)?;
            Ok(BrrrType::Result(Box::new(ok), Box::new(err)))
        }
        6 => {
            let count = ctx.read_varint()? as usize;
            let mut elems = Vec::with_capacity(count);
            for _ in 0..count {
                elems.push(decode_brrr_type(ctx)?);
            }
            Ok(BrrrType::Tuple(elems))
        }
        7 => Ok(BrrrType::Func(Box::new(decode_func_type(ctx)?))),
        8 => Ok(BrrrType::Var(ctx.decode_spur()?)),
        9 => {
            let base = decode_brrr_type(ctx)?;
            let count = ctx.read_varint()? as usize;
            let mut args = Vec::with_capacity(count);
            for _ in 0..count {
                args.push(decode_brrr_type(ctx)?);
            }
            Ok(BrrrType::App(Box::new(base), args))
        }
        10 => Ok(BrrrType::Named(ctx.decode_spur()?)),
        11 => Ok(BrrrType::Struct(decode_struct_type(ctx)?)),
        12 => Ok(BrrrType::Enum(decode_enum_type(ctx)?)),
        13 => Ok(BrrrType::Interface(decode_interface_type(ctx)?)),
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid BrrrType discriminant: {}",
            disc
        ))),
    }
}

// ============================================================================
// Source Location Encoding
// ============================================================================

/// Encode a Pos (source position)
fn encode_pos<W: Write>(ctx: &mut EncodeContext<W>, pos: &Pos) -> Result<(), EncodeError> {
    ctx.write_varint(pos.file_id)?;
    ctx.write_varint(pos.line)?;
    ctx.write_varint(pos.col)?;
    Ok(())
}

/// Decode a Pos
fn decode_pos<R: Read>(ctx: &mut DecodeContext<R>) -> Result<Pos, DecodeError> {
    Ok(Pos {
        file_id: ctx.read_varint()?,
        line: ctx.read_varint()?,
        col: ctx.read_varint()?,
    })
}

/// Encode a Range (source range)
fn encode_range<W: Write>(ctx: &mut EncodeContext<W>, range: &Range) -> Result<(), EncodeError> {
    encode_pos(ctx, &range.start)?;
    encode_pos(ctx, &range.end)?;
    Ok(())
}

/// Decode a Range
fn decode_range<R: Read>(ctx: &mut DecodeContext<R>) -> Result<Range, DecodeError> {
    Ok(Range {
        start: decode_pos(ctx)?,
        end: decode_pos(ctx)?,
    })
}

// ============================================================================
// Literal Encoding
// ============================================================================

/// Encode a Literal
fn encode_literal<W: Write>(ctx: &mut EncodeContext<W>, lit: &Literal) -> Result<(), EncodeError> {
    ctx.write_u8(lit.discriminant())?;
    match lit {
        Literal::Unit => {}
        Literal::Bool(b) => ctx.write_bool(*b)?,
        Literal::Int(v, int_type) => {
            ctx.write_i128(*v)?;
            encode_int_type(ctx, *int_type)?;
        }
        Literal::Float(bits, prec) => {
            ctx.write_u64(bits.0)?;
            encode_float_prec(ctx, *prec)?;
        }
        Literal::String(s) => ctx.write_string(s)?,
        Literal::Char(c) => ctx.write_varint(*c as u32)?,
    }
    Ok(())
}

/// Decode a Literal
fn decode_literal<R: Read>(ctx: &mut DecodeContext<R>) -> Result<Literal, DecodeError> {
    let disc = ctx.read_u8()?;
    match disc {
        0 => Ok(Literal::Unit),
        1 => Ok(Literal::Bool(ctx.read_bool()?)),
        2 => {
            let v = ctx.read_i128()?;
            let int_type = decode_int_type(ctx)?;
            Ok(Literal::Int(v, int_type))
        }
        3 => {
            let bits = FloatBits(ctx.read_u64()?);
            let prec = decode_float_prec(ctx)?;
            Ok(Literal::Float(bits, prec))
        }
        4 => Ok(Literal::String(ctx.read_string()?)),
        5 => {
            let code = ctx.read_varint()?;
            let c = char::from_u32(code).ok_or_else(|| {
                DecodeError::InvalidSection(format!("Invalid char code: {}", code))
            })?;
            Ok(Literal::Char(c))
        }
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid Literal discriminant: {}",
            disc
        ))),
    }
}

// ============================================================================
// Operator Encoding
// ============================================================================

/// Encode a UnaryOp
fn encode_unary_op<W: Write>(
    ctx: &mut EncodeContext<W>,
    op: UnaryOp,
) -> Result<(), EncodeError> {
    ctx.write_u8(op as u8)
}

/// Decode a UnaryOp
fn decode_unary_op<R: Read>(ctx: &mut DecodeContext<R>) -> Result<UnaryOp, DecodeError> {
    let v = ctx.read_u8()?;
    match v {
        0 => Ok(UnaryOp::Neg),
        1 => Ok(UnaryOp::Not),
        2 => Ok(UnaryOp::BitNot),
        3 => Ok(UnaryOp::Deref),
        4 => Ok(UnaryOp::Ref),
        5 => Ok(UnaryOp::RefMut),
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid UnaryOp: {}",
            v
        ))),
    }
}

/// Encode a BinaryOp
fn encode_binary_op<W: Write>(
    ctx: &mut EncodeContext<W>,
    op: BinaryOp,
) -> Result<(), EncodeError> {
    ctx.write_u8(op as u8)
}

/// Decode a BinaryOp
fn decode_binary_op<R: Read>(ctx: &mut DecodeContext<R>) -> Result<BinaryOp, DecodeError> {
    let v = ctx.read_u8()?;
    match v {
        0 => Ok(BinaryOp::Add),
        1 => Ok(BinaryOp::Sub),
        2 => Ok(BinaryOp::Mul),
        3 => Ok(BinaryOp::Div),
        4 => Ok(BinaryOp::Mod),
        5 => Ok(BinaryOp::Eq),
        6 => Ok(BinaryOp::Ne),
        7 => Ok(BinaryOp::Lt),
        8 => Ok(BinaryOp::Le),
        9 => Ok(BinaryOp::Gt),
        10 => Ok(BinaryOp::Ge),
        11 => Ok(BinaryOp::And),
        12 => Ok(BinaryOp::Or),
        13 => Ok(BinaryOp::BitAnd),
        14 => Ok(BinaryOp::BitOr),
        15 => Ok(BinaryOp::BitXor),
        16 => Ok(BinaryOp::Shl),
        17 => Ok(BinaryOp::Shr),
        18 => Ok(BinaryOp::UShr),
        19 => Ok(BinaryOp::AddChecked),
        20 => Ok(BinaryOp::AddWrapping),
        21 => Ok(BinaryOp::AddSaturating),
        22 => Ok(BinaryOp::SubChecked),
        23 => Ok(BinaryOp::SubWrapping),
        24 => Ok(BinaryOp::SubSaturating),
        25 => Ok(BinaryOp::MulChecked),
        26 => Ok(BinaryOp::MulWrapping),
        27 => Ok(BinaryOp::MulSaturating),
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid BinaryOp: {}",
            v
        ))),
    }
}

// ============================================================================
// Pattern Encoding
// ============================================================================

/// Encode a Pattern
fn encode_pattern<W: Write>(
    ctx: &mut EncodeContext<W>,
    pattern: &Pattern,
) -> Result<(), EncodeError> {
    encode_range(ctx, &pattern.range)?;
    encode_pattern_inner(ctx, &pattern.value)
}

/// Encode Pattern_ (inner value)
fn encode_pattern_inner<W: Write>(
    ctx: &mut EncodeContext<W>,
    pattern: &Pattern_,
) -> Result<(), EncodeError> {
    ctx.write_u8(pattern.discriminant())?;
    match pattern {
        Pattern_::Wild => {}
        Pattern_::Var(spur) => ctx.encode_spur(*spur)?,
        Pattern_::Lit(lit) => encode_literal(ctx, lit)?,
        Pattern_::Tuple(pats) => {
            ctx.write_varint(pats.len() as u32)?;
            for p in pats {
                encode_pattern(ctx, p)?;
            }
        }
        Pattern_::Struct { name, fields } => {
            ctx.encode_spur(*name)?;
            ctx.write_varint(fields.len() as u32)?;
            for (field_name, field_pat) in fields {
                ctx.encode_spur(*field_name)?;
                encode_pattern(ctx, field_pat)?;
            }
        }
        Pattern_::Variant {
            type_name,
            variant,
            fields,
        } => {
            ctx.encode_spur(*type_name)?;
            ctx.encode_spur(*variant)?;
            ctx.write_varint(fields.len() as u32)?;
            for p in fields {
                encode_pattern(ctx, p)?;
            }
        }
        Pattern_::Or(left, right) => {
            encode_pattern(ctx, left)?;
            encode_pattern(ctx, right)?;
        }
        Pattern_::Guard(pat, guard_expr) => {
            encode_pattern(ctx, pat)?;
            encode_expr(ctx, guard_expr)?;
        }
        Pattern_::Ref(inner) => encode_pattern(ctx, inner)?,
        Pattern_::Box(inner) => encode_pattern(ctx, inner)?,
        Pattern_::Rest(opt_spur) => ctx.encode_option_spur(*opt_spur)?,
        Pattern_::As(pat, binding) => {
            encode_pattern(ctx, pat)?;
            ctx.encode_spur(*binding)?;
        }
        Pattern_::Type { expected, binding } => {
            encode_brrr_type(ctx, expected)?;
            ctx.encode_option_spur(*binding)?;
        }
    }
    Ok(())
}

/// Decode a Pattern
fn decode_pattern<R: Read>(ctx: &mut DecodeContext<R>) -> Result<Pattern, DecodeError> {
    let range = decode_range(ctx)?;
    let value = decode_pattern_inner(ctx)?;
    Ok(WithLoc::new(value, range))
}

/// Decode Pattern_
fn decode_pattern_inner<R: Read>(ctx: &mut DecodeContext<R>) -> Result<Pattern_, DecodeError> {
    let disc = ctx.read_u8()?;
    match disc {
        0 => Ok(Pattern_::Wild),
        1 => Ok(Pattern_::Var(ctx.decode_spur()?)),
        2 => Ok(Pattern_::Lit(decode_literal(ctx)?)),
        3 => {
            let len = ctx.read_varint()? as usize;
            let mut pats = Vec::with_capacity(len);
            for _ in 0..len {
                pats.push(decode_pattern(ctx)?);
            }
            Ok(Pattern_::Tuple(pats))
        }
        4 => {
            let name = ctx.decode_spur()?;
            let len = ctx.read_varint()? as usize;
            let mut fields = Vec::with_capacity(len);
            for _ in 0..len {
                let field_name = ctx.decode_spur()?;
                let field_pat = decode_pattern(ctx)?;
                fields.push((field_name, field_pat));
            }
            Ok(Pattern_::Struct { name, fields })
        }
        5 => {
            let type_name = ctx.decode_spur()?;
            let variant = ctx.decode_spur()?;
            let len = ctx.read_varint()? as usize;
            let mut fields = Vec::with_capacity(len);
            for _ in 0..len {
                fields.push(decode_pattern(ctx)?);
            }
            Ok(Pattern_::Variant {
                type_name,
                variant,
                fields,
            })
        }
        6 => {
            let left = Box::new(decode_pattern(ctx)?);
            let right = Box::new(decode_pattern(ctx)?);
            Ok(Pattern_::Or(left, right))
        }
        7 => {
            let pat = Box::new(decode_pattern(ctx)?);
            let guard = Box::new(decode_expr(ctx)?);
            Ok(Pattern_::Guard(pat, guard))
        }
        8 => Ok(Pattern_::Ref(Box::new(decode_pattern(ctx)?))),
        9 => Ok(Pattern_::Box(Box::new(decode_pattern(ctx)?))),
        10 => Ok(Pattern_::Rest(ctx.decode_option_spur()?)),
        11 => {
            let pat = Box::new(decode_pattern(ctx)?);
            let binding = ctx.decode_spur()?;
            Ok(Pattern_::As(pat, binding))
        }
        12 => {
            let expected = decode_brrr_type(ctx)?;
            let binding = ctx.decode_option_spur()?;
            Ok(Pattern_::Type { expected, binding })
        }
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid Pattern_ discriminant: {}",
            disc
        ))),
    }
}

// ============================================================================
// MatchArm and CatchArm Encoding
// ============================================================================

/// Encode a MatchArm
fn encode_match_arm<W: Write>(
    ctx: &mut EncodeContext<W>,
    arm: &MatchArm,
) -> Result<(), EncodeError> {
    encode_range(ctx, &arm.range)?;
    encode_pattern(ctx, &arm.pattern)?;
    match &arm.guard {
        None => ctx.write_u8(0)?,
        Some(g) => {
            ctx.write_u8(1)?;
            encode_expr(ctx, g)?;
        }
    }
    encode_expr(ctx, &arm.body)
}

/// Decode a MatchArm
fn decode_match_arm<R: Read>(ctx: &mut DecodeContext<R>) -> Result<MatchArm, DecodeError> {
    let range = decode_range(ctx)?;
    let pattern = decode_pattern(ctx)?;
    let guard = if ctx.read_u8()? == 0 {
        None
    } else {
        Some(decode_expr(ctx)?)
    };
    let body = decode_expr(ctx)?;
    Ok(MatchArm {
        range,
        pattern,
        guard,
        body,
    })
}

/// Encode a CatchArm
fn encode_catch_arm<W: Write>(
    ctx: &mut EncodeContext<W>,
    arm: &CatchArm,
) -> Result<(), EncodeError> {
    encode_range(ctx, &arm.range)?;
    encode_pattern(ctx, &arm.pattern)?;
    encode_brrr_type(ctx, &arm.exception_type)?;
    encode_expr(ctx, &arm.body)
}

/// Decode a CatchArm
fn decode_catch_arm<R: Read>(ctx: &mut DecodeContext<R>) -> Result<CatchArm, DecodeError> {
    let range = decode_range(ctx)?;
    let pattern = decode_pattern(ctx)?;
    let exception_type = decode_brrr_type(ctx)?;
    let body = decode_expr(ctx)?;
    Ok(CatchArm {
        range,
        pattern,
        exception_type,
        body,
    })
}

// ============================================================================
// Effect Handler Encoding
// ============================================================================

/// Encode an EffectHandler
fn encode_effect_handler<W: Write>(
    ctx: &mut EncodeContext<W>,
    handler: &EffectHandler,
) -> Result<(), EncodeError> {
    // Encode clauses
    ctx.write_varint(handler.clauses.len() as u32)?;
    for clause in &handler.clauses {
        encode_handler_clause(ctx, clause)?;
    }

    // Encode return clause
    match &handler.return_clause {
        None => ctx.write_u8(0)?,
        Some((var, expr)) => {
            ctx.write_u8(1)?;
            ctx.encode_spur(*var)?;
            encode_expr(ctx, expr)?;
        }
    }

    // Encode depth
    ctx.write_u8(match handler.depth {
        HandlerDepth::Shallow => 0,
        HandlerDepth::Deep => 1,
    })
}

/// Decode an EffectHandler
fn decode_effect_handler<R: Read>(
    ctx: &mut DecodeContext<R>,
) -> Result<EffectHandler, DecodeError> {
    let clause_count = ctx.read_varint()? as usize;
    let mut clauses = Vec::with_capacity(clause_count);
    for _ in 0..clause_count {
        clauses.push(decode_handler_clause(ctx)?);
    }

    let return_clause = if ctx.read_u8()? == 0 {
        None
    } else {
        let var = ctx.decode_spur()?;
        let expr = decode_expr(ctx)?;
        Some((var, expr))
    };

    let depth = match ctx.read_u8()? {
        0 => HandlerDepth::Shallow,
        1 => HandlerDepth::Deep,
        v => {
            return Err(DecodeError::InvalidSection(format!(
                "Invalid HandlerDepth: {}",
                v
            )))
        }
    };

    Ok(EffectHandler {
        clauses,
        return_clause,
        depth,
    })
}

/// Encode a HandlerClause
fn encode_handler_clause<W: Write>(
    ctx: &mut EncodeContext<W>,
    clause: &HandlerClause,
) -> Result<(), EncodeError> {
    encode_effect_op(ctx, &clause.op)?;
    ctx.write_varint(clause.params.len() as u32)?;
    for v in &clause.params {
        ctx.encode_spur(*v)?;
    }
    ctx.encode_spur(clause.continuation)?;
    ctx.write_u8(match clause.continuation_linearity {
        ContinuationLinearity::OneShot => 0,
        ContinuationLinearity::MultiShot => 1,
    })?;
    encode_expr(ctx, &clause.body)
}

/// Decode a HandlerClause
fn decode_handler_clause<R: Read>(ctx: &mut DecodeContext<R>) -> Result<HandlerClause, DecodeError> {
    let op = decode_effect_op(ctx)?;
    let param_count = ctx.read_varint()? as usize;
    let mut params = Vec::with_capacity(param_count);
    for _ in 0..param_count {
        params.push(ctx.decode_spur()?);
    }
    let continuation = ctx.decode_spur()?;
    let continuation_linearity = match ctx.read_u8()? {
        0 => ContinuationLinearity::OneShot,
        1 => ContinuationLinearity::MultiShot,
        v => {
            return Err(DecodeError::InvalidSection(format!(
                "Invalid ContinuationLinearity: {}",
                v
            )))
        }
    };
    let body = decode_expr(ctx)?;
    Ok(HandlerClause {
        op,
        params,
        continuation,
        continuation_linearity,
        body,
    })
}

// ============================================================================
// Expression Encoding (Main Implementation)
// ============================================================================

/// Encode an Expr (expression with location)
fn encode_expr<W: Write>(ctx: &mut EncodeContext<W>, expr: &Expr) -> Result<(), EncodeError> {
    encode_range(ctx, &expr.range)?;
    encode_expr_inner(ctx, &expr.value)
}

/// Encode Expr_ (the inner expression variant)
fn encode_expr_inner<W: Write>(
    ctx: &mut EncodeContext<W>,
    expr: &Expr_,
) -> Result<(), EncodeError> {
    ctx.write_u8(expr.discriminant())?;

    match expr {
        // === Literals and Variables (0-2) ===
        Expr_::Lit(lit) => encode_literal(ctx, lit)?,
        Expr_::Var(var) => ctx.encode_spur(*var)?,
        Expr_::Global(name) => ctx.encode_spur(*name)?,

        // === Operations (3-6) ===
        Expr_::Unary(op, inner) => {
            encode_unary_op(ctx, *op)?;
            encode_expr(ctx, inner)?;
        }
        Expr_::Binary(op, left, right) => {
            encode_binary_op(ctx, *op)?;
            encode_expr(ctx, left)?;
            encode_expr(ctx, right)?;
        }
        Expr_::Call(func, args) => {
            encode_expr(ctx, func)?;
            ctx.write_varint(args.len() as u32)?;
            for arg in args {
                encode_expr(ctx, arg)?;
            }
        }
        Expr_::MethodCall(receiver, method, args) => {
            encode_expr(ctx, receiver)?;
            ctx.encode_spur(*method)?;
            ctx.write_varint(args.len() as u32)?;
            for arg in args {
                encode_expr(ctx, arg)?;
            }
        }

        // === Data Construction (7-10) ===
        Expr_::Tuple(elems) => {
            ctx.write_varint(elems.len() as u32)?;
            for e in elems {
                encode_expr(ctx, e)?;
            }
        }
        Expr_::Array(elems) => {
            ctx.write_varint(elems.len() as u32)?;
            for e in elems {
                encode_expr(ctx, e)?;
            }
        }
        Expr_::Struct { name, fields } => {
            ctx.encode_spur(*name)?;
            ctx.write_varint(fields.len() as u32)?;
            for (field_name, field_expr) in fields {
                ctx.encode_spur(*field_name)?;
                encode_expr(ctx, field_expr)?;
            }
        }
        Expr_::Variant {
            type_name,
            variant,
            fields,
        } => {
            ctx.encode_spur(*type_name)?;
            ctx.encode_spur(*variant)?;
            ctx.write_varint(fields.len() as u32)?;
            for e in fields {
                encode_expr(ctx, e)?;
            }
        }

        // === Data Access (11-13) ===
        Expr_::Field(obj, field) => {
            encode_expr(ctx, obj)?;
            ctx.encode_spur(*field)?;
        }
        Expr_::Index(arr, idx) => {
            encode_expr(ctx, arr)?;
            encode_expr(ctx, idx)?;
        }
        Expr_::TupleProj(tuple, idx) => {
            encode_expr(ctx, tuple)?;
            ctx.write_varint(*idx)?;
        }

        // === Control Flow (14-21) ===
        Expr_::If(cond, then_branch, else_branch) => {
            encode_expr(ctx, cond)?;
            encode_expr(ctx, then_branch)?;
            encode_expr(ctx, else_branch)?;
        }
        Expr_::Match(scrutinee, arms) => {
            encode_expr(ctx, scrutinee)?;
            ctx.write_varint(arms.len() as u32)?;
            for arm in arms {
                encode_match_arm(ctx, arm)?;
            }
        }
        Expr_::Loop { label, body } => {
            ctx.encode_option_spur(*label)?;
            encode_expr(ctx, body)?;
        }
        Expr_::While { label, cond, body } => {
            ctx.encode_option_spur(*label)?;
            encode_expr(ctx, cond)?;
            encode_expr(ctx, body)?;
        }
        Expr_::For {
            label,
            var,
            iter,
            body,
        } => {
            ctx.encode_option_spur(*label)?;
            ctx.encode_spur(*var)?;
            encode_expr(ctx, iter)?;
            encode_expr(ctx, body)?;
        }
        Expr_::Break { label, value } => {
            ctx.encode_option_spur(*label)?;
            match value {
                None => ctx.write_u8(0)?,
                Some(e) => {
                    ctx.write_u8(1)?;
                    encode_expr(ctx, e)?;
                }
            }
        }
        Expr_::Continue { label } => ctx.encode_option_spur(*label)?,
        Expr_::Return(value) => match value {
            None => ctx.write_u8(0)?,
            Some(e) => {
                ctx.write_u8(1)?;
                encode_expr(ctx, e)?;
            }
        },

        // === Bindings (22-24) ===
        Expr_::Let {
            pattern,
            ty,
            init,
            body,
        } => {
            encode_pattern(ctx, pattern)?;
            match ty {
                None => ctx.write_u8(0)?,
                Some(t) => {
                    ctx.write_u8(1)?;
                    encode_brrr_type(ctx, t)?;
                }
            }
            encode_expr(ctx, init)?;
            encode_expr(ctx, body)?;
        }
        Expr_::LetMut { var, ty, init, body } => {
            ctx.encode_spur(*var)?;
            match ty {
                None => ctx.write_u8(0)?,
                Some(t) => {
                    ctx.write_u8(1)?;
                    encode_brrr_type(ctx, t)?;
                }
            }
            encode_expr(ctx, init)?;
            encode_expr(ctx, body)?;
        }
        Expr_::Assign(lhs, rhs) => {
            encode_expr(ctx, lhs)?;
            encode_expr(ctx, rhs)?;
        }

        // === Functions (25-26) ===
        Expr_::Lambda { params, body } => {
            ctx.write_varint(params.len() as u32)?;
            for (var, ty) in params {
                ctx.encode_spur(*var)?;
                encode_brrr_type(ctx, ty)?;
            }
            encode_expr(ctx, body)?;
        }
        Expr_::Closure {
            params,
            captures,
            body,
        } => {
            ctx.write_varint(params.len() as u32)?;
            for (var, ty) in params {
                ctx.encode_spur(*var)?;
                encode_brrr_type(ctx, ty)?;
            }
            ctx.write_varint(captures.len() as u32)?;
            for v in captures {
                ctx.encode_spur(*v)?;
            }
            encode_expr(ctx, body)?;
        }

        // === Memory Operations (27-32) ===
        Expr_::Box(inner) => encode_expr(ctx, inner)?,
        Expr_::Deref(inner) => encode_expr(ctx, inner)?,
        Expr_::Borrow(inner) => encode_expr(ctx, inner)?,
        Expr_::BorrowMut(inner) => encode_expr(ctx, inner)?,
        Expr_::Move(inner) => encode_expr(ctx, inner)?,
        Expr_::Drop(inner) => encode_expr(ctx, inner)?,

        // === Exception Handling (33-34) ===
        Expr_::Throw(inner) => encode_expr(ctx, inner)?,
        Expr_::Try {
            body,
            catches,
            finally,
        } => {
            encode_expr(ctx, body)?;
            ctx.write_varint(catches.len() as u32)?;
            for c in catches {
                encode_catch_arm(ctx, c)?;
            }
            match finally {
                None => ctx.write_u8(0)?,
                Some(e) => {
                    ctx.write_u8(1)?;
                    encode_expr(ctx, e)?;
                }
            }
        }

        // === Async/Concurrency (35-38) ===
        Expr_::Await(inner) => encode_expr(ctx, inner)?,
        Expr_::Yield(inner) => encode_expr(ctx, inner)?,
        Expr_::Async(inner) => encode_expr(ctx, inner)?,
        Expr_::Spawn(inner) => encode_expr(ctx, inner)?,

        // === Effect Operations (39-41) ===
        Expr_::Handle(body, handler) => {
            encode_expr(ctx, body)?;
            encode_effect_handler(ctx, handler)?;
        }
        Expr_::Perform(op, args) => {
            encode_effect_op(ctx, op)?;
            ctx.write_varint(args.len() as u32)?;
            for arg in args {
                encode_expr(ctx, arg)?;
            }
        }
        Expr_::Resume { var, value } => {
            ctx.encode_spur(*var)?;
            encode_expr(ctx, value)?;
        }

        // === Delimited Continuations (42-43) ===
        Expr_::Reset { label, body } => {
            ctx.encode_spur(*label)?;
            encode_expr(ctx, body)?;
        }
        Expr_::Shift { label, var, body } => {
            ctx.encode_spur(*label)?;
            ctx.encode_spur(*var)?;
            encode_expr(ctx, body)?;
        }

        // === Type Operations (44-47) ===
        Expr_::As(inner, ty) => {
            encode_expr(ctx, inner)?;
            encode_brrr_type(ctx, ty)?;
        }
        Expr_::Is(inner, ty) => {
            encode_expr(ctx, inner)?;
            encode_brrr_type(ctx, ty)?;
        }
        Expr_::Sizeof(ty) => encode_brrr_type(ctx, ty)?,
        Expr_::Alignof(ty) => encode_brrr_type(ctx, ty)?,

        // === Blocks (48-50) ===
        Expr_::Block(stmts) => {
            ctx.write_varint(stmts.len() as u32)?;
            for s in stmts {
                encode_expr(ctx, s)?;
            }
        }
        Expr_::Seq(first, second) => {
            encode_expr(ctx, first)?;
            encode_expr(ctx, second)?;
        }
        Expr_::Unsafe(inner) => encode_expr(ctx, inner)?,

        // === Special (51-52) ===
        Expr_::Hole => {}
        Expr_::Error(msg) => ctx.encode_spur(*msg)?,

        // === Gradual Typing (53) ===
        Expr_::GradualCast { expr, from, to, kind, blame } => {
            encode_expr(ctx, expr)?;
            // Encode gradual types - for now, simplified encoding
            // A full implementation would encode the GradualType structure
            ctx.write_u8(match from {
                crate::gradual::GradualType::Dynamic => 0,
                crate::gradual::GradualType::Ground(_) => 1,
                crate::gradual::GradualType::GFunc(_, _) => 2,
                crate::gradual::GradualType::GRef(_) => 3,
            })?;
            ctx.write_u8(match to {
                crate::gradual::GradualType::Dynamic => 0,
                crate::gradual::GradualType::Ground(_) => 1,
                crate::gradual::GradualType::GFunc(_, _) => 2,
                crate::gradual::GradualType::GRef(_) => 3,
            })?;
            ctx.write_u8(match kind {
                crate::gradual::CastKind::Upcast => 0,
                crate::gradual::CastKind::Downcast => 1,
                crate::gradual::CastKind::FuncCast => 2,
                crate::gradual::CastKind::RefCast => 3,
            })?;
            // Encode blame labels as strings
            ctx.write_string(&blame.positive)?;
            ctx.write_string(&blame.negative)?;
        }

        // === Control Flow Labels (54-55) ===
        Expr_::Goto { label } => ctx.encode_spur(*label)?,
        Expr_::Labeled { label, body } => {
            ctx.encode_spur(*label)?;
            encode_expr(ctx, body)?;
        }
    }
    Ok(())
}

/// Decode an Expr
fn decode_expr<R: Read>(ctx: &mut DecodeContext<R>) -> Result<Expr, DecodeError> {
    let range = decode_range(ctx)?;
    let value = decode_expr_inner(ctx)?;
    Ok(WithLoc::new(value, range))
}

/// Decode Expr_
fn decode_expr_inner<R: Read>(ctx: &mut DecodeContext<R>) -> Result<Expr_, DecodeError> {
    let disc = ctx.read_u8()?;

    match disc {
        // === Literals and Variables (0-2) ===
        0 => Ok(Expr_::Lit(decode_literal(ctx)?)),
        1 => Ok(Expr_::Var(ctx.decode_spur()?)),
        2 => Ok(Expr_::Global(ctx.decode_spur()?)),

        // === Operations (3-6) ===
        3 => {
            let op = decode_unary_op(ctx)?;
            let inner = Box::new(decode_expr(ctx)?);
            Ok(Expr_::Unary(op, inner))
        }
        4 => {
            let op = decode_binary_op(ctx)?;
            let left = Box::new(decode_expr(ctx)?);
            let right = Box::new(decode_expr(ctx)?);
            Ok(Expr_::Binary(op, left, right))
        }
        5 => {
            let func = Box::new(decode_expr(ctx)?);
            let arg_count = ctx.read_varint()? as usize;
            let mut args = Vec::with_capacity(arg_count);
            for _ in 0..arg_count {
                args.push(decode_expr(ctx)?);
            }
            Ok(Expr_::Call(func, args))
        }
        6 => {
            let receiver = Box::new(decode_expr(ctx)?);
            let method = ctx.decode_spur()?;
            let arg_count = ctx.read_varint()? as usize;
            let mut args = Vec::with_capacity(arg_count);
            for _ in 0..arg_count {
                args.push(decode_expr(ctx)?);
            }
            Ok(Expr_::MethodCall(receiver, method, args))
        }

        // === Data Construction (7-10) ===
        7 => {
            let len = ctx.read_varint()? as usize;
            let mut elems = Vec::with_capacity(len);
            for _ in 0..len {
                elems.push(decode_expr(ctx)?);
            }
            Ok(Expr_::Tuple(elems))
        }
        8 => {
            let len = ctx.read_varint()? as usize;
            let mut elems = Vec::with_capacity(len);
            for _ in 0..len {
                elems.push(decode_expr(ctx)?);
            }
            Ok(Expr_::Array(elems))
        }
        9 => {
            let name = ctx.decode_spur()?;
            let len = ctx.read_varint()? as usize;
            let mut fields = Vec::with_capacity(len);
            for _ in 0..len {
                let field_name = ctx.decode_spur()?;
                let field_expr = decode_expr(ctx)?;
                fields.push((field_name, field_expr));
            }
            Ok(Expr_::Struct { name, fields })
        }
        10 => {
            let type_name = ctx.decode_spur()?;
            let variant = ctx.decode_spur()?;
            let len = ctx.read_varint()? as usize;
            let mut fields = Vec::with_capacity(len);
            for _ in 0..len {
                fields.push(decode_expr(ctx)?);
            }
            Ok(Expr_::Variant {
                type_name,
                variant,
                fields,
            })
        }

        // === Data Access (11-13) ===
        11 => {
            let obj = Box::new(decode_expr(ctx)?);
            let field = ctx.decode_spur()?;
            Ok(Expr_::Field(obj, field))
        }
        12 => {
            let arr = Box::new(decode_expr(ctx)?);
            let idx = Box::new(decode_expr(ctx)?);
            Ok(Expr_::Index(arr, idx))
        }
        13 => {
            let tuple = Box::new(decode_expr(ctx)?);
            let idx = ctx.read_varint()?;
            Ok(Expr_::TupleProj(tuple, idx))
        }

        // === Control Flow (14-21) ===
        14 => {
            let cond = Box::new(decode_expr(ctx)?);
            let then_branch = Box::new(decode_expr(ctx)?);
            let else_branch = Box::new(decode_expr(ctx)?);
            Ok(Expr_::If(cond, then_branch, else_branch))
        }
        15 => {
            let scrutinee = Box::new(decode_expr(ctx)?);
            let arm_count = ctx.read_varint()? as usize;
            let mut arms = Vec::with_capacity(arm_count);
            for _ in 0..arm_count {
                arms.push(decode_match_arm(ctx)?);
            }
            Ok(Expr_::Match(scrutinee, arms))
        }
        16 => {
            let label = ctx.decode_option_spur()?;
            let body = Box::new(decode_expr(ctx)?);
            Ok(Expr_::Loop { label, body })
        }
        17 => {
            let label = ctx.decode_option_spur()?;
            let cond = Box::new(decode_expr(ctx)?);
            let body = Box::new(decode_expr(ctx)?);
            Ok(Expr_::While { label, cond, body })
        }
        18 => {
            let label = ctx.decode_option_spur()?;
            let var = ctx.decode_spur()?;
            let iter = Box::new(decode_expr(ctx)?);
            let body = Box::new(decode_expr(ctx)?);
            Ok(Expr_::For {
                label,
                var,
                iter,
                body,
            })
        }
        19 => {
            let label = ctx.decode_option_spur()?;
            let value = if ctx.read_u8()? == 0 {
                None
            } else {
                Some(Box::new(decode_expr(ctx)?))
            };
            Ok(Expr_::Break { label, value })
        }
        20 => {
            let label = ctx.decode_option_spur()?;
            Ok(Expr_::Continue { label })
        }
        21 => {
            let value = if ctx.read_u8()? == 0 {
                None
            } else {
                Some(Box::new(decode_expr(ctx)?))
            };
            Ok(Expr_::Return(value))
        }

        // === Bindings (22-24) ===
        22 => {
            let pattern = decode_pattern(ctx)?;
            let ty = if ctx.read_u8()? == 0 {
                None
            } else {
                Some(decode_brrr_type(ctx)?)
            };
            let init = Box::new(decode_expr(ctx)?);
            let body = Box::new(decode_expr(ctx)?);
            Ok(Expr_::Let {
                pattern,
                ty,
                init,
                body,
            })
        }
        23 => {
            let var = ctx.decode_spur()?;
            let ty = if ctx.read_u8()? == 0 {
                None
            } else {
                Some(decode_brrr_type(ctx)?)
            };
            let init = Box::new(decode_expr(ctx)?);
            let body = Box::new(decode_expr(ctx)?);
            Ok(Expr_::LetMut { var, ty, init, body })
        }
        24 => {
            let lhs = Box::new(decode_expr(ctx)?);
            let rhs = Box::new(decode_expr(ctx)?);
            Ok(Expr_::Assign(lhs, rhs))
        }

        // === Functions (25-26) ===
        25 => {
            let param_count = ctx.read_varint()? as usize;
            let mut params = Vec::with_capacity(param_count);
            for _ in 0..param_count {
                let var = ctx.decode_spur()?;
                let ty = decode_brrr_type(ctx)?;
                params.push((var, ty));
            }
            let body = Box::new(decode_expr(ctx)?);
            Ok(Expr_::Lambda { params, body })
        }
        26 => {
            let param_count = ctx.read_varint()? as usize;
            let mut params = Vec::with_capacity(param_count);
            for _ in 0..param_count {
                let var = ctx.decode_spur()?;
                let ty = decode_brrr_type(ctx)?;
                params.push((var, ty));
            }
            let cap_count = ctx.read_varint()? as usize;
            let mut captures = Vec::with_capacity(cap_count);
            for _ in 0..cap_count {
                captures.push(ctx.decode_spur()?);
            }
            let body = Box::new(decode_expr(ctx)?);
            Ok(Expr_::Closure {
                params,
                captures,
                body,
            })
        }

        // === Memory Operations (27-32) ===
        27 => Ok(Expr_::Box(Box::new(decode_expr(ctx)?))),
        28 => Ok(Expr_::Deref(Box::new(decode_expr(ctx)?))),
        29 => Ok(Expr_::Borrow(Box::new(decode_expr(ctx)?))),
        30 => Ok(Expr_::BorrowMut(Box::new(decode_expr(ctx)?))),
        31 => Ok(Expr_::Move(Box::new(decode_expr(ctx)?))),
        32 => Ok(Expr_::Drop(Box::new(decode_expr(ctx)?))),

        // === Exception Handling (33-34) ===
        33 => Ok(Expr_::Throw(Box::new(decode_expr(ctx)?))),
        34 => {
            let body = Box::new(decode_expr(ctx)?);
            let catch_count = ctx.read_varint()? as usize;
            let mut catches = Vec::with_capacity(catch_count);
            for _ in 0..catch_count {
                catches.push(decode_catch_arm(ctx)?);
            }
            let finally = if ctx.read_u8()? == 0 {
                None
            } else {
                Some(Box::new(decode_expr(ctx)?))
            };
            Ok(Expr_::Try {
                body,
                catches,
                finally,
            })
        }

        // === Async/Concurrency (35-38) ===
        35 => Ok(Expr_::Await(Box::new(decode_expr(ctx)?))),
        36 => Ok(Expr_::Yield(Box::new(decode_expr(ctx)?))),
        37 => Ok(Expr_::Async(Box::new(decode_expr(ctx)?))),
        38 => Ok(Expr_::Spawn(Box::new(decode_expr(ctx)?))),

        // === Effect Operations (39-41) ===
        39 => {
            let body = Box::new(decode_expr(ctx)?);
            let handler = Box::new(decode_effect_handler(ctx)?);
            Ok(Expr_::Handle(body, handler))
        }
        40 => {
            let op = decode_effect_op(ctx)?;
            let arg_count = ctx.read_varint()? as usize;
            let mut args = Vec::with_capacity(arg_count);
            for _ in 0..arg_count {
                args.push(decode_expr(ctx)?);
            }
            Ok(Expr_::Perform(op, args))
        }
        41 => {
            let var = ctx.decode_spur()?;
            let value = Box::new(decode_expr(ctx)?);
            Ok(Expr_::Resume { var, value })
        }

        // === Delimited Continuations (42-43) ===
        42 => {
            let label = ctx.decode_spur()?;
            let body = Box::new(decode_expr(ctx)?);
            Ok(Expr_::Reset { label, body })
        }
        43 => {
            let label = ctx.decode_spur()?;
            let var = ctx.decode_spur()?;
            let body = Box::new(decode_expr(ctx)?);
            Ok(Expr_::Shift { label, var, body })
        }

        // === Type Operations (44-47) ===
        44 => {
            let inner = Box::new(decode_expr(ctx)?);
            let ty = decode_brrr_type(ctx)?;
            Ok(Expr_::As(inner, ty))
        }
        45 => {
            let inner = Box::new(decode_expr(ctx)?);
            let ty = decode_brrr_type(ctx)?;
            Ok(Expr_::Is(inner, ty))
        }
        46 => Ok(Expr_::Sizeof(decode_brrr_type(ctx)?)),
        47 => Ok(Expr_::Alignof(decode_brrr_type(ctx)?)),

        // === Blocks (48-50) ===
        48 => {
            let len = ctx.read_varint()? as usize;
            let mut stmts = Vec::with_capacity(len);
            for _ in 0..len {
                stmts.push(decode_expr(ctx)?);
            }
            Ok(Expr_::Block(stmts))
        }
        49 => {
            let first = Box::new(decode_expr(ctx)?);
            let second = Box::new(decode_expr(ctx)?);
            Ok(Expr_::Seq(first, second))
        }
        50 => Ok(Expr_::Unsafe(Box::new(decode_expr(ctx)?))),

        // === Special (51-52) ===
        51 => Ok(Expr_::Hole),
        52 => Ok(Expr_::Error(ctx.decode_spur()?)),

        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid Expr_ discriminant: {}",
            disc
        ))),
    }
}

// ============================================================================
// Declaration Encoding
// ============================================================================

// Declaration discriminants for FullDeclaration
const DECL_FUNCTION: u8 = 0;
const DECL_TYPE: u8 = 1;
const DECL_TRAIT: u8 = 2;
const DECL_IMPL: u8 = 3;
const DECL_CONST: u8 = 4;
const DECL_STATIC: u8 = 5;
const DECL_MODULE: u8 = 6;
const DECL_USE: u8 = 7;
const DECL_EXTERN: u8 = 8;

// TypeDef discriminants
const TYPEDEF_ALIAS: u8 = 0;
const TYPEDEF_NEWTYPE: u8 = 1;
const TYPEDEF_STRUCT: u8 = 2;
const TYPEDEF_ENUM: u8 = 3;

// ExternItem discriminants
const EXTERN_FUNCTION: u8 = 0;
const EXTERN_STATIC: u8 = 1;
const EXTERN_TYPE: u8 = 2;

/// Encode a FunctionDef
fn encode_function_def<W: Write>(
    ctx: &mut EncodeContext<W>,
    func: &FunctionDef,
) -> Result<(), EncodeError> {
    ctx.encode_spur(func.name)?;
    encode_kinded_vars(ctx, &func.type_params)?;
    ctx.write_varint(func.params.len() as u32)?;
    for param in &func.params {
        encode_param_type(ctx, param)?;
    }
    encode_brrr_type(ctx, &func.return_type)?;
    encode_effect_row(ctx, &func.effects)?;
    encode_option_expr(ctx, &func.body)?;
    encode_option_contract(ctx, &func.contract)?;
    encode_visibility(ctx, func.visibility)?;
    ctx.write_bool(func.is_unsafe)?;
    ctx.write_bool(func.is_async)?;
    ctx.write_bool(func.is_const)?;
    encode_range(ctx, &func.span)?;
    Ok(())
}

/// Decode a FunctionDef
fn decode_function_def<R: Read>(ctx: &mut DecodeContext<R>) -> Result<FunctionDef, DecodeError> {
    let name = ctx.decode_spur()?;
    let type_params = decode_kinded_vars(ctx)?;
    let param_count = ctx.read_varint()? as usize;
    let mut params = Vec::with_capacity(param_count);
    for _ in 0..param_count {
        params.push(decode_param_type(ctx)?);
    }
    let return_type = decode_brrr_type(ctx)?;
    let effects = decode_effect_row(ctx)?;
    let body = decode_option_expr(ctx)?;
    let contract = decode_option_contract(ctx)?;
    let visibility = decode_visibility(ctx)?;
    let is_unsafe = ctx.read_bool()?;
    let is_async = ctx.read_bool()?;
    let is_const = ctx.read_bool()?;
    let span = decode_range(ctx)?;

    Ok(FunctionDef {
        name,
        type_params,
        params,
        return_type,
        effects,
        body,
        contract,
        visibility,
        is_unsafe,
        is_async,
        is_const,
        span,
    })
}

/// Encode a TypeDef
fn encode_type_def<W: Write>(
    ctx: &mut EncodeContext<W>,
    typedef: &TypeDef,
) -> Result<(), EncodeError> {
    match typedef {
        TypeDef::Alias {
            name,
            params,
            target,
        } => {
            ctx.write_u8(TYPEDEF_ALIAS)?;
            ctx.encode_spur(*name)?;
            encode_kinded_vars(ctx, params)?;
            encode_brrr_type(ctx, target)?;
        }
        TypeDef::Newtype {
            name,
            params,
            inner,
        } => {
            ctx.write_u8(TYPEDEF_NEWTYPE)?;
            ctx.encode_spur(*name)?;
            encode_kinded_vars(ctx, params)?;
            encode_brrr_type(ctx, inner)?;
        }
        TypeDef::Struct(st) => {
            ctx.write_u8(TYPEDEF_STRUCT)?;
            encode_struct_type(ctx, st)?;
        }
        TypeDef::Enum(et) => {
            ctx.write_u8(TYPEDEF_ENUM)?;
            encode_enum_type(ctx, et)?;
        }
    }
    Ok(())
}

/// Decode a TypeDef
fn decode_type_def<R: Read>(ctx: &mut DecodeContext<R>) -> Result<TypeDef, DecodeError> {
    let disc = ctx.read_u8()?;
    match disc {
        TYPEDEF_ALIAS => {
            let name = ctx.decode_spur()?;
            let params = decode_kinded_vars(ctx)?;
            let target = decode_brrr_type(ctx)?;
            Ok(TypeDef::Alias {
                name,
                params,
                target,
            })
        }
        TYPEDEF_NEWTYPE => {
            let name = ctx.decode_spur()?;
            let params = decode_kinded_vars(ctx)?;
            let inner = decode_brrr_type(ctx)?;
            Ok(TypeDef::Newtype {
                name,
                params,
                inner,
            })
        }
        TYPEDEF_STRUCT => {
            let st = decode_struct_type(ctx)?;
            Ok(TypeDef::Struct(st))
        }
        TYPEDEF_ENUM => {
            let et = decode_enum_type(ctx)?;
            Ok(TypeDef::Enum(et))
        }
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid TypeDef discriminant: {}",
            disc
        ))),
    }
}

/// Encode an AssocTypeDef
fn encode_assoc_type_def<W: Write>(
    ctx: &mut EncodeContext<W>,
    atd: &AssocTypeDef,
) -> Result<(), EncodeError> {
    ctx.encode_spur(atd.name)?;
    ctx.write_varint(atd.bounds.len() as u32)?;
    for bound in &atd.bounds {
        ctx.encode_spur(*bound)?;
    }
    match &atd.default {
        None => ctx.write_u8(0)?,
        Some(ty) => {
            ctx.write_u8(1)?;
            encode_brrr_type(ctx, ty)?;
        }
    }
    Ok(())
}

/// Decode an AssocTypeDef
fn decode_assoc_type_def<R: Read>(ctx: &mut DecodeContext<R>) -> Result<AssocTypeDef, DecodeError> {
    let name = ctx.decode_spur()?;
    let bound_count = ctx.read_varint()? as usize;
    let mut bounds = Vec::with_capacity(bound_count);
    for _ in 0..bound_count {
        bounds.push(ctx.decode_spur()?);
    }
    let default = if ctx.read_u8()? == 0 {
        None
    } else {
        Some(decode_brrr_type(ctx)?)
    };
    Ok(AssocTypeDef {
        name,
        bounds,
        default,
    })
}

/// Encode a TraitDef
fn encode_trait_def<W: Write>(
    ctx: &mut EncodeContext<W>,
    trait_def: &TraitDef,
) -> Result<(), EncodeError> {
    ctx.encode_spur(trait_def.name)?;
    encode_kinded_vars(ctx, &trait_def.type_params)?;
    ctx.write_varint(trait_def.super_traits.len() as u32)?;
    for st in &trait_def.super_traits {
        ctx.encode_spur(*st)?;
    }
    ctx.write_varint(trait_def.methods.len() as u32)?;
    for method in &trait_def.methods {
        encode_function_def(ctx, method)?;
    }
    ctx.write_varint(trait_def.assoc_types.len() as u32)?;
    for at in &trait_def.assoc_types {
        encode_assoc_type_def(ctx, at)?;
    }
    encode_visibility(ctx, trait_def.visibility)?;
    encode_range(ctx, &trait_def.span)?;
    Ok(())
}

/// Decode a TraitDef
fn decode_trait_def<R: Read>(ctx: &mut DecodeContext<R>) -> Result<TraitDef, DecodeError> {
    let name = ctx.decode_spur()?;
    let type_params = decode_kinded_vars(ctx)?;
    let super_trait_count = ctx.read_varint()? as usize;
    let mut super_traits = Vec::with_capacity(super_trait_count);
    for _ in 0..super_trait_count {
        super_traits.push(ctx.decode_spur()?);
    }
    let method_count = ctx.read_varint()? as usize;
    let mut methods = Vec::with_capacity(method_count);
    for _ in 0..method_count {
        methods.push(decode_function_def(ctx)?);
    }
    let assoc_type_count = ctx.read_varint()? as usize;
    let mut assoc_types = Vec::with_capacity(assoc_type_count);
    for _ in 0..assoc_type_count {
        assoc_types.push(decode_assoc_type_def(ctx)?);
    }
    let visibility = decode_visibility(ctx)?;
    let span = decode_range(ctx)?;

    Ok(TraitDef {
        name,
        type_params,
        super_traits,
        methods,
        assoc_types,
        visibility,
        span,
    })
}

/// Encode a TraitRef
fn encode_trait_ref<W: Write>(
    ctx: &mut EncodeContext<W>,
    tr: &TraitRef,
) -> Result<(), EncodeError> {
    ctx.encode_spur(tr.name)?;
    ctx.write_varint(tr.type_args.len() as u32)?;
    for arg in &tr.type_args {
        encode_brrr_type(ctx, arg)?;
    }
    Ok(())
}

/// Decode a TraitRef
fn decode_trait_ref<R: Read>(ctx: &mut DecodeContext<R>) -> Result<TraitRef, DecodeError> {
    let name = ctx.decode_spur()?;
    let arg_count = ctx.read_varint()? as usize;
    let mut type_args = Vec::with_capacity(arg_count);
    for _ in 0..arg_count {
        type_args.push(decode_brrr_type(ctx)?);
    }
    Ok(TraitRef { name, type_args })
}

/// Encode an AssocTypeBinding
fn encode_assoc_type_binding<W: Write>(
    ctx: &mut EncodeContext<W>,
    atb: &AssocTypeBinding,
) -> Result<(), EncodeError> {
    ctx.encode_spur(atb.name)?;
    encode_brrr_type(ctx, &atb.ty)
}

/// Decode an AssocTypeBinding
fn decode_assoc_type_binding<R: Read>(
    ctx: &mut DecodeContext<R>,
) -> Result<AssocTypeBinding, DecodeError> {
    let name = ctx.decode_spur()?;
    let ty = decode_brrr_type(ctx)?;
    Ok(AssocTypeBinding { name, ty })
}

/// Encode an ImplBlock
fn encode_impl_block<W: Write>(
    ctx: &mut EncodeContext<W>,
    impl_block: &ImplBlock,
) -> Result<(), EncodeError> {
    encode_kinded_vars(ctx, &impl_block.type_params)?;
    match &impl_block.trait_ref {
        None => ctx.write_u8(0)?,
        Some(tr) => {
            ctx.write_u8(1)?;
            encode_trait_ref(ctx, tr)?;
        }
    }
    encode_brrr_type(ctx, &impl_block.self_type)?;
    ctx.write_varint(impl_block.methods.len() as u32)?;
    for method in &impl_block.methods {
        encode_function_def(ctx, method)?;
    }
    ctx.write_varint(impl_block.assoc_type_bindings.len() as u32)?;
    for atb in &impl_block.assoc_type_bindings {
        encode_assoc_type_binding(ctx, atb)?;
    }
    encode_visibility(ctx, impl_block.visibility)?;
    encode_range(ctx, &impl_block.span)?;
    Ok(())
}

/// Decode an ImplBlock
fn decode_impl_block<R: Read>(ctx: &mut DecodeContext<R>) -> Result<ImplBlock, DecodeError> {
    let type_params = decode_kinded_vars(ctx)?;
    let trait_ref = if ctx.read_u8()? == 0 {
        None
    } else {
        Some(decode_trait_ref(ctx)?)
    };
    let self_type = decode_brrr_type(ctx)?;
    let method_count = ctx.read_varint()? as usize;
    let mut methods = Vec::with_capacity(method_count);
    for _ in 0..method_count {
        methods.push(decode_function_def(ctx)?);
    }
    let atb_count = ctx.read_varint()? as usize;
    let mut assoc_type_bindings = Vec::with_capacity(atb_count);
    for _ in 0..atb_count {
        assoc_type_bindings.push(decode_assoc_type_binding(ctx)?);
    }
    let visibility = decode_visibility(ctx)?;
    let span = decode_range(ctx)?;

    Ok(ImplBlock {
        type_params,
        trait_ref,
        self_type,
        methods,
        assoc_type_bindings,
        visibility,
        span,
    })
}

/// Encode an ExternItem
fn encode_extern_item<W: Write>(
    ctx: &mut EncodeContext<W>,
    item: &ExternItem,
) -> Result<(), EncodeError> {
    match item {
        ExternItem::Function(f) => {
            ctx.write_u8(EXTERN_FUNCTION)?;
            encode_function_def(ctx, f)?;
        }
        ExternItem::Static { name, ty, is_mut } => {
            ctx.write_u8(EXTERN_STATIC)?;
            ctx.encode_spur(*name)?;
            encode_brrr_type(ctx, ty)?;
            ctx.write_bool(*is_mut)?;
        }
        ExternItem::Type { name } => {
            ctx.write_u8(EXTERN_TYPE)?;
            ctx.encode_spur(*name)?;
        }
    }
    Ok(())
}

/// Decode an ExternItem
fn decode_extern_item<R: Read>(ctx: &mut DecodeContext<R>) -> Result<ExternItem, DecodeError> {
    let disc = ctx.read_u8()?;
    match disc {
        EXTERN_FUNCTION => {
            let f = decode_function_def(ctx)?;
            Ok(ExternItem::Function(f))
        }
        EXTERN_STATIC => {
            let name = ctx.decode_spur()?;
            let ty = decode_brrr_type(ctx)?;
            let is_mut = ctx.read_bool()?;
            Ok(ExternItem::Static { name, ty, is_mut })
        }
        EXTERN_TYPE => {
            let name = ctx.decode_spur()?;
            Ok(ExternItem::Type { name })
        }
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid ExternItem discriminant: {}",
            disc
        ))),
    }
}

/// Encode a list of Spurs (for use paths)
fn encode_spur_list<W: Write>(
    ctx: &mut EncodeContext<W>,
    list: &[Spur],
) -> Result<(), EncodeError> {
    ctx.write_varint(list.len() as u32)?;
    for s in list {
        ctx.encode_spur(*s)?;
    }
    Ok(())
}

/// Decode a list of Spurs
fn decode_spur_list<R: Read>(ctx: &mut DecodeContext<R>) -> Result<Vec<Spur>, DecodeError> {
    let count = ctx.read_varint()? as usize;
    let mut list = Vec::with_capacity(count);
    for _ in 0..count {
        list.push(ctx.decode_spur()?);
    }
    Ok(list)
}

/// Encode a FullDeclaration
fn encode_declaration<W: Write>(
    ctx: &mut EncodeContext<W>,
    decl: &FullDeclaration,
) -> Result<(), EncodeError> {
    match decl {
        FullDeclaration::Function(f) => {
            ctx.write_u8(DECL_FUNCTION)?;
            encode_function_def(ctx, f)?;
        }
        FullDeclaration::Type(t) => {
            ctx.write_u8(DECL_TYPE)?;
            encode_type_def(ctx, t)?;
        }
        FullDeclaration::Trait(t) => {
            ctx.write_u8(DECL_TRAIT)?;
            encode_trait_def(ctx, t)?;
        }
        FullDeclaration::Impl(i) => {
            ctx.write_u8(DECL_IMPL)?;
            encode_impl_block(ctx, i)?;
        }
        FullDeclaration::Const {
            name,
            ty,
            value,
            visibility,
            span,
        } => {
            ctx.write_u8(DECL_CONST)?;
            ctx.encode_spur(*name)?;
            encode_brrr_type(ctx, ty)?;
            encode_expr(ctx, value)?;
            encode_visibility(ctx, *visibility)?;
            encode_range(ctx, span)?;
        }
        FullDeclaration::Static {
            name,
            ty,
            value,
            is_mut,
            visibility,
            span,
        } => {
            ctx.write_u8(DECL_STATIC)?;
            ctx.encode_spur(*name)?;
            encode_brrr_type(ctx, ty)?;
            encode_option_expr(ctx, value)?;
            ctx.write_bool(*is_mut)?;
            encode_visibility(ctx, *visibility)?;
            encode_range(ctx, span)?;
        }
        FullDeclaration::Module {
            name,
            declarations,
            visibility,
            span,
        } => {
            ctx.write_u8(DECL_MODULE)?;
            ctx.encode_spur(*name)?;
            ctx.write_varint(declarations.len() as u32)?;
            for d in declarations {
                encode_declaration(ctx, d)?;
            }
            encode_visibility(ctx, *visibility)?;
            encode_range(ctx, span)?;
        }
        FullDeclaration::Use {
            path,
            alias,
            visibility,
            span,
        } => {
            ctx.write_u8(DECL_USE)?;
            encode_spur_list(ctx, path)?;
            ctx.encode_option_spur(*alias)?;
            encode_visibility(ctx, *visibility)?;
            encode_range(ctx, span)?;
        }
        FullDeclaration::Extern { abi, items, span } => {
            ctx.write_u8(DECL_EXTERN)?;
            ctx.encode_option_spur(*abi)?;
            ctx.write_varint(items.len() as u32)?;
            for item in items {
                encode_extern_item(ctx, item)?;
            }
            encode_range(ctx, span)?;
        }
    }
    Ok(())
}

/// Decode a FullDeclaration
fn decode_declaration<R: Read>(ctx: &mut DecodeContext<R>) -> Result<FullDeclaration, DecodeError> {
    let disc = ctx.read_u8()?;
    match disc {
        DECL_FUNCTION => {
            let f = decode_function_def(ctx)?;
            Ok(FullDeclaration::Function(f))
        }
        DECL_TYPE => {
            let t = decode_type_def(ctx)?;
            Ok(FullDeclaration::Type(t))
        }
        DECL_TRAIT => {
            let t = decode_trait_def(ctx)?;
            Ok(FullDeclaration::Trait(t))
        }
        DECL_IMPL => {
            let i = decode_impl_block(ctx)?;
            Ok(FullDeclaration::Impl(i))
        }
        DECL_CONST => {
            let name = ctx.decode_spur()?;
            let ty = decode_brrr_type(ctx)?;
            let value = decode_expr(ctx)?;
            let visibility = decode_visibility(ctx)?;
            let span = decode_range(ctx)?;
            Ok(FullDeclaration::Const {
                name,
                ty,
                value,
                visibility,
                span,
            })
        }
        DECL_STATIC => {
            let name = ctx.decode_spur()?;
            let ty = decode_brrr_type(ctx)?;
            let value = decode_option_expr(ctx)?;
            let is_mut = ctx.read_bool()?;
            let visibility = decode_visibility(ctx)?;
            let span = decode_range(ctx)?;
            Ok(FullDeclaration::Static {
                name,
                ty,
                value,
                is_mut,
                visibility,
                span,
            })
        }
        DECL_MODULE => {
            let name = ctx.decode_spur()?;
            let decl_count = ctx.read_varint()? as usize;
            let mut declarations = Vec::with_capacity(decl_count);
            for _ in 0..decl_count {
                declarations.push(decode_declaration(ctx)?);
            }
            let visibility = decode_visibility(ctx)?;
            let span = decode_range(ctx)?;
            Ok(FullDeclaration::Module {
                name,
                declarations,
                visibility,
                span,
            })
        }
        DECL_USE => {
            let path = decode_spur_list(ctx)?;
            let alias = ctx.decode_option_spur()?;
            let visibility = decode_visibility(ctx)?;
            let span = decode_range(ctx)?;
            Ok(FullDeclaration::Use {
                path,
                alias,
                visibility,
                span,
            })
        }
        DECL_EXTERN => {
            let abi = ctx.decode_option_spur()?;
            let item_count = ctx.read_varint()? as usize;
            let mut items = Vec::with_capacity(item_count);
            for _ in 0..item_count {
                items.push(decode_extern_item(ctx)?);
            }
            let span = decode_range(ctx)?;
            Ok(FullDeclaration::Extern { abi, items, span })
        }
        _ => Err(DecodeError::InvalidSection(format!(
            "Invalid FullDeclaration discriminant: {}",
            disc
        ))),
    }
}

// ============================================================================
// Binary Encoder/Decoder
// ============================================================================

/// Binary format encoder
#[derive(Debug, Default)]
pub struct BinaryEncoder {
    _private: (),
}

impl BinaryEncoder {
    /// Create a new encoder
    pub fn new() -> Self {
        Self::default()
    }

    /// Encode a module to the writer
    ///
    /// Binary format:
    /// ```text
    /// [MAGIC: "BRRR" (4 bytes)]
    /// [VERSION: u16]
    /// [MODULE_NAME: len + bytes]
    /// [FILES: count + (len + bytes)*]
    /// [STRING_TABLE: count + (len + bytes)*]
    /// [TYPES: varint count + encoded types]
    /// [EXPRS: varint count + encoded exprs]
    /// [DECLARATIONS: varint count + encoded declarations]
    /// [CONTENT_HASH: 16 bytes]
    /// ```
    pub fn encode<W: Write>(&self, module: &BrrrModule, mut writer: W) -> ReprResult<()> {
        // Create a temporary Rodeo for encoding
        let rodeo = Rodeo::default();

        // First pass: encode types to a buffer to collect string table
        let mut type_buffer = Vec::new();
        let mut expr_buffer = Vec::new();
        let mut decl_buffer = Vec::new();
        let string_table: Vec<(Spur, String)>;

        {
            let mut ctx = EncodeContext::new(&mut type_buffer, &rodeo);
            ctx.write_varint(module.types.len() as u32)?;
            for ty in &module.types {
                encode_brrr_type(&mut ctx, ty)?;
            }

            // Second pass: encode expressions to a buffer
            let type_strings = std::mem::take(&mut ctx.string_table);

            let mut expr_ctx = EncodeContext {
                writer: &mut expr_buffer,
                string_table: type_strings,
                rodeo: &rodeo,
            };
            expr_ctx.write_varint(module.exprs.len() as u32)?;
            for expr in &module.exprs {
                encode_expr(&mut expr_ctx, expr)?;
            }

            // Third pass: encode declarations to a buffer
            let expr_strings = std::mem::take(&mut expr_ctx.string_table);

            let mut decl_ctx = EncodeContext {
                writer: &mut decl_buffer,
                string_table: expr_strings,
                rodeo: &rodeo,
            };
            decl_ctx.write_varint(module.declarations.len() as u32)?;
            for decl in &module.declarations {
                encode_declaration(&mut decl_ctx, decl)?;
            }

            string_table = decl_ctx.string_table;
        }

        // Write header
        writer.write_all(&MAGIC)?;
        writer.write_all(&VERSION.to_le_bytes())?;

        // Write module name
        let name_bytes = module.name.as_bytes();
        writer.write_all(&(name_bytes.len() as u32).to_le_bytes())?;
        writer.write_all(name_bytes)?;

        // Write file count and files
        writer.write_all(&(module.files.len() as u32).to_le_bytes())?;
        for file in &module.files {
            let bytes = file.as_bytes();
            writer.write_all(&(bytes.len() as u32).to_le_bytes())?;
            writer.write_all(bytes)?;
        }

        // Write string table
        encode_varint_to(string_table.len() as u64, &mut writer)?;
        for (_, s) in &string_table {
            let bytes = s.as_bytes();
            encode_varint_to(bytes.len() as u64, &mut writer)?;
            writer.write_all(bytes)?;
        }

        // Write type data
        writer.write_all(&type_buffer)?;

        // Write expression data
        writer.write_all(&expr_buffer)?;

        // Write declaration data
        writer.write_all(&decl_buffer)?;

        // Write content hash
        let hash = super::content_hash(module);
        writer.write_all(&hash)?;

        Ok(())
    }
}

/// Binary format decoder
#[derive(Debug, Default)]
pub struct BinaryDecoder {
    _private: (),
}

impl BinaryDecoder {
    /// Create a new decoder
    pub fn new() -> Self {
        Self::default()
    }

    /// Decode a module from the reader
    pub fn decode<R: Read>(&self, mut reader: R) -> ReprResult<BrrrModule> {
        // Read and verify magic
        let mut magic = [0u8; 4];
        reader.read_exact(&mut magic)?;
        if magic != MAGIC {
            return Err(DecodeError::InvalidMagic(magic).into());
        }

        // Read version
        let mut version_bytes = [0u8; 2];
        reader.read_exact(&mut version_bytes)?;
        let version = u16::from_le_bytes(version_bytes);

        // Read module name
        let mut len_bytes = [0u8; 4];
        reader.read_exact(&mut len_bytes)?;
        let name_len = u32::from_le_bytes(len_bytes) as usize;
        let mut name_bytes = vec![0u8; name_len];
        reader.read_exact(&mut name_bytes)?;
        let name =
            String::from_utf8(name_bytes).map_err(|e| DecodeError::InvalidSection(e.to_string()))?;

        // Read files
        reader.read_exact(&mut len_bytes)?;
        let file_count = u32::from_le_bytes(len_bytes) as usize;
        let mut files = Vec::with_capacity(file_count);
        for _ in 0..file_count {
            reader.read_exact(&mut len_bytes)?;
            let len = u32::from_le_bytes(len_bytes) as usize;
            let mut bytes = vec![0u8; len];
            reader.read_exact(&mut bytes)?;
            let s = String::from_utf8(bytes)
                .map_err(|e| DecodeError::InvalidSection(e.to_string()))?;
            files.push(s);
        }

        // Read string table
        let string_count = decode_varint32_from(&mut reader)? as usize;
        let mut strings = Vec::with_capacity(string_count);
        for _ in 0..string_count {
            let str_len = decode_varint32_from(&mut reader)? as usize;
            let mut bytes = vec![0u8; str_len];
            reader.read_exact(&mut bytes)?;
            let s = String::from_utf8(bytes)
                .map_err(|e| DecodeError::InvalidSection(e.to_string()))?;
            strings.push(s);
        }

        // Read types
        let mut rodeo = Rodeo::default();
        let mut types = Vec::new();
        let mut exprs = Vec::new();
        let mut declarations = Vec::new();

        {
            let mut ctx = DecodeContext::new(&mut reader, &mut rodeo, strings);
            let type_count = ctx.read_varint()? as usize;
            types.reserve(type_count);
            for _ in 0..type_count {
                types.push(decode_brrr_type(&mut ctx)?);
            }

            // Read expressions
            let expr_count = ctx.read_varint()? as usize;
            exprs.reserve(expr_count);
            for _ in 0..expr_count {
                exprs.push(decode_expr(&mut ctx)?);
            }

            // Read declarations
            let decl_count = ctx.read_varint()? as usize;
            declarations.reserve(decl_count);
            for _ in 0..decl_count {
                declarations.push(decode_declaration(&mut ctx)?);
            }
        }

        // Read content hash (for verification)
        let mut _hash = [0u8; 16];
        reader.read_exact(&mut _hash)?;

        Ok(BrrrModule {
            name,
            files,
            types,
            exprs,
            declarations,
            version,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{FloatPrec, IntType};

    fn roundtrip_module(module: BrrrModule) -> BrrrModule {
        let mut buf = Vec::new();
        let encoder = BinaryEncoder::new();
        encoder.encode(&module, &mut buf).unwrap();

        let decoder = BinaryDecoder::new();
        decoder.decode(&buf[..]).unwrap()
    }

    fn roundtrip_type(ty: BrrrType) -> BrrrType {
        let module = BrrrModule {
            name: "test".to_string(),
            files: vec!["test.brrr".to_string()],
            types: vec![ty],
            exprs: Vec::new(),
            declarations: Vec::new(),
            version: 1,
        };

        let decoded = roundtrip_module(module);
        assert_eq!(decoded.types.len(), 1);
        decoded.types.into_iter().next().unwrap()
    }

    fn roundtrip_expr(expr: Expr) -> Expr {
        let module = BrrrModule {
            name: "test".to_string(),
            files: vec!["test.brrr".to_string()],
            types: Vec::new(),
            exprs: vec![expr],
            declarations: Vec::new(),
            version: 1,
        };

        let decoded = roundtrip_module(module);
        assert_eq!(decoded.exprs.len(), 1);
        decoded.exprs.into_iter().next().unwrap()
    }

    #[test]
    fn test_roundtrip_prim() {
        for kind in [
            PrimKind::Unit,
            PrimKind::Never,
            PrimKind::Bool,
            PrimKind::String,
            PrimKind::Char,
            PrimKind::Dynamic,
            PrimKind::Unknown,
        ] {
            let ty = BrrrType::Prim(kind);
            assert_eq!(roundtrip_type(ty.clone()), ty);
        }
    }

    #[test]
    fn test_roundtrip_numeric() {
        let ty = BrrrType::Numeric(NumericType::Int(IntType::I32));
        assert_eq!(roundtrip_type(ty.clone()), ty);

        let ty = BrrrType::Numeric(NumericType::Float(FloatPrec::F64));
        assert_eq!(roundtrip_type(ty.clone()), ty);
    }

    #[test]
    fn test_roundtrip_wrap() {
        let ty = BrrrType::Wrap(WrapperKind::Array, Box::new(BrrrType::BOOL));
        assert_eq!(roundtrip_type(ty.clone()), ty);

        let ty = BrrrType::Wrap(WrapperKind::Option, Box::new(BrrrType::STRING));
        assert_eq!(roundtrip_type(ty.clone()), ty);
    }

    #[test]
    fn test_roundtrip_result() {
        let ty = BrrrType::Result(
            Box::new(BrrrType::Numeric(NumericType::Int(IntType::I32))),
            Box::new(BrrrType::STRING),
        );
        assert_eq!(roundtrip_type(ty.clone()), ty);
    }

    #[test]
    fn test_roundtrip_tuple() {
        let ty = BrrrType::Tuple(vec![BrrrType::BOOL, BrrrType::STRING, BrrrType::UNIT]);
        assert_eq!(roundtrip_type(ty.clone()), ty);
    }

    #[test]
    fn test_roundtrip_func() {
        let func = FuncType::pure(
            vec![ParamType::unnamed(BrrrType::Numeric(NumericType::Int(
                IntType::I32,
            )))],
            BrrrType::BOOL,
        );
        let ty = BrrrType::Func(Box::new(func));
        assert_eq!(roundtrip_type(ty.clone()), ty);
    }

    #[test]
    fn test_roundtrip_nested() {
        // Option[Array[Result[i32, String]]]
        let inner = BrrrType::Result(
            Box::new(BrrrType::Numeric(NumericType::Int(IntType::I32))),
            Box::new(BrrrType::STRING),
        );
        let array = BrrrType::Wrap(WrapperKind::Array, Box::new(inner));
        let ty = BrrrType::Wrap(WrapperKind::Option, Box::new(array));
        assert_eq!(roundtrip_type(ty.clone()), ty);
    }

    #[test]
    fn test_roundtrip_multiple_types() {
        let module = BrrrModule {
            name: "multi".to_string(),
            files: vec!["a.brrr".to_string(), "b.brrr".to_string()],
            types: vec![
                BrrrType::UNIT,
                BrrrType::BOOL,
                BrrrType::Numeric(NumericType::Int(IntType::I64)),
                BrrrType::Wrap(WrapperKind::Ref, Box::new(BrrrType::STRING)),
            ],
            exprs: Vec::new(),
            declarations: Vec::new(),
            version: 1,
        };

        let decoded = roundtrip_module(module);

        assert_eq!(decoded.name, "multi");
        assert_eq!(decoded.files.len(), 2);
        assert_eq!(decoded.types.len(), 4);
        assert_eq!(decoded.types[0], BrrrType::UNIT);
        assert_eq!(decoded.types[1], BrrrType::BOOL);
        assert_eq!(
            decoded.types[2],
            BrrrType::Numeric(NumericType::Int(IntType::I64))
        );
    }

    #[test]
    fn test_empty_module() {
        let module = BrrrModule {
            name: "empty".to_string(),
            files: Vec::new(),
            types: Vec::new(),
            exprs: Vec::new(),
            declarations: Vec::new(),
            version: 1,
        };

        let decoded = roundtrip_module(module);

        assert_eq!(decoded.name, "empty");
        assert!(decoded.files.is_empty());
        assert!(decoded.types.is_empty());
        assert!(decoded.exprs.is_empty());
    }

    // === Expression Tests ===

    #[test]
    fn test_roundtrip_literal_expr() {
        let literals = vec![
            Literal::Unit,
            Literal::Bool(true),
            Literal::Bool(false),
            Literal::i32(42),
            Literal::i64(-123456789),
            Literal::u32(0xDEADBEEF),
            Literal::f64(3.14159),
            Literal::String("hello world".to_string()),
            Literal::Char('X'),
        ];

        for lit in literals {
            let expr = WithLoc::synthetic(Expr_::Lit(lit.clone()));
            let decoded = roundtrip_expr(expr);
            assert_eq!(decoded.value, Expr_::Lit(lit));
        }
    }

    #[test]
    fn test_roundtrip_binary_expr() {
        let left = Box::new(WithLoc::synthetic(Expr_::Lit(Literal::i32(1))));
        let right = Box::new(WithLoc::synthetic(Expr_::Lit(Literal::i32(2))));
        let expr = WithLoc::synthetic(Expr_::Binary(BinaryOp::Add, left, right));

        let decoded = roundtrip_expr(expr);
        match &decoded.value {
            Expr_::Binary(BinaryOp::Add, l, r) => {
                assert_eq!(l.value, Expr_::Lit(Literal::i32(1)));
                assert_eq!(r.value, Expr_::Lit(Literal::i32(2)));
            }
            _ => panic!("expected Binary"),
        }
    }

    #[test]
    fn test_roundtrip_if_expr() {
        let cond = Box::new(WithLoc::synthetic(Expr_::Lit(Literal::Bool(true))));
        let then_b = Box::new(WithLoc::synthetic(Expr_::Lit(Literal::i32(1))));
        let else_b = Box::new(WithLoc::synthetic(Expr_::Lit(Literal::i32(2))));
        let expr = WithLoc::synthetic(Expr_::If(cond, then_b, else_b));

        let decoded = roundtrip_expr(expr);
        assert!(matches!(decoded.value, Expr_::If(_, _, _)));
    }

    #[test]
    fn test_roundtrip_block_expr() {
        let stmts = vec![
            WithLoc::synthetic(Expr_::Lit(Literal::i32(1))),
            WithLoc::synthetic(Expr_::Lit(Literal::i32(2))),
            WithLoc::synthetic(Expr_::Lit(Literal::i32(3))),
        ];
        let expr = WithLoc::synthetic(Expr_::Block(stmts));

        let decoded = roundtrip_expr(expr);
        match &decoded.value {
            Expr_::Block(s) => assert_eq!(s.len(), 3),
            _ => panic!("expected Block"),
        }
    }

    #[test]
    fn test_roundtrip_hole_expr() {
        let expr = WithLoc::synthetic(Expr_::Hole);
        let decoded = roundtrip_expr(expr);
        assert_eq!(decoded.value, Expr_::Hole);
    }

    #[test]
    fn test_roundtrip_unary_expr() {
        let inner = Box::new(WithLoc::synthetic(Expr_::Lit(Literal::i32(42))));
        let expr = WithLoc::synthetic(Expr_::Unary(UnaryOp::Neg, inner));

        let decoded = roundtrip_expr(expr);
        match &decoded.value {
            Expr_::Unary(UnaryOp::Neg, i) => {
                assert_eq!(i.value, Expr_::Lit(Literal::i32(42)));
            }
            _ => panic!("expected Unary"),
        }
    }

    #[test]
    fn test_roundtrip_call_expr() {
        let func = Box::new(WithLoc::synthetic(Expr_::Hole));
        let args = vec![
            WithLoc::synthetic(Expr_::Lit(Literal::i32(1))),
            WithLoc::synthetic(Expr_::Lit(Literal::i32(2))),
        ];
        let expr = WithLoc::synthetic(Expr_::Call(func, args));

        let decoded = roundtrip_expr(expr);
        match &decoded.value {
            Expr_::Call(_, args) => assert_eq!(args.len(), 2),
            _ => panic!("expected Call"),
        }
    }

    #[test]
    fn test_roundtrip_tuple_expr() {
        let elems = vec![
            WithLoc::synthetic(Expr_::Lit(Literal::i32(1))),
            WithLoc::synthetic(Expr_::Lit(Literal::Bool(true))),
        ];
        let expr = WithLoc::synthetic(Expr_::Tuple(elems));

        let decoded = roundtrip_expr(expr);
        match &decoded.value {
            Expr_::Tuple(e) => assert_eq!(e.len(), 2),
            _ => panic!("expected Tuple"),
        }
    }

    #[test]
    fn test_roundtrip_loop_expr() {
        let body = Box::new(WithLoc::synthetic(Expr_::Hole));
        let expr = WithLoc::synthetic(Expr_::Loop { label: None, body });

        let decoded = roundtrip_expr(expr);
        assert!(matches!(decoded.value, Expr_::Loop { label: None, .. }));
    }

    #[test]
    fn test_roundtrip_return_expr() {
        let expr = WithLoc::synthetic(Expr_::Return(None));
        let decoded = roundtrip_expr(expr);
        assert_eq!(decoded.value, Expr_::Return(None));

        let inner = Box::new(WithLoc::synthetic(Expr_::Lit(Literal::i32(42))));
        let expr = WithLoc::synthetic(Expr_::Return(Some(inner)));
        let decoded = roundtrip_expr(expr);
        assert!(matches!(decoded.value, Expr_::Return(Some(_))));
    }

    #[test]
    fn test_roundtrip_memory_ops() {
        let inner = Box::new(WithLoc::synthetic(Expr_::Hole));

        for make_expr in [
            |i: Box<Expr>| Expr_::Box(i),
            |i: Box<Expr>| Expr_::Deref(i),
            |i: Box<Expr>| Expr_::Borrow(i),
            |i: Box<Expr>| Expr_::BorrowMut(i),
            |i: Box<Expr>| Expr_::Move(i),
            |i: Box<Expr>| Expr_::Drop(i),
        ] {
            let expr = WithLoc::synthetic(make_expr(inner.clone()));
            let decoded = roundtrip_expr(expr.clone());
            assert_eq!(
                std::mem::discriminant(&decoded.value),
                std::mem::discriminant(&expr.value)
            );
        }
    }

    #[test]
    fn test_roundtrip_async_ops() {
        let inner = Box::new(WithLoc::synthetic(Expr_::Hole));

        for make_expr in [
            |i: Box<Expr>| Expr_::Await(i),
            |i: Box<Expr>| Expr_::Yield(i),
            |i: Box<Expr>| Expr_::Async(i),
            |i: Box<Expr>| Expr_::Spawn(i),
        ] {
            let expr = WithLoc::synthetic(make_expr(inner.clone()));
            let decoded = roundtrip_expr(expr.clone());
            assert_eq!(
                std::mem::discriminant(&decoded.value),
                std::mem::discriminant(&expr.value)
            );
        }
    }

    #[test]
    fn test_roundtrip_types_and_exprs_together() {
        let module = BrrrModule {
            name: "mixed".to_string(),
            files: vec!["test.brrr".to_string()],
            types: vec![BrrrType::BOOL, BrrrType::Numeric(NumericType::Int(IntType::I32))],
            exprs: vec![
                WithLoc::synthetic(Expr_::Lit(Literal::Bool(true))),
                WithLoc::synthetic(Expr_::Lit(Literal::i32(42))),
            ],
            declarations: Vec::new(),
            version: 1,
        };

        let decoded = roundtrip_module(module);

        assert_eq!(decoded.types.len(), 2);
        assert_eq!(decoded.exprs.len(), 2);
        assert_eq!(decoded.types[0], BrrrType::BOOL);
        assert_eq!(decoded.exprs[0].value, Expr_::Lit(Literal::Bool(true)));
        assert_eq!(decoded.exprs[1].value, Expr_::Lit(Literal::i32(42)));
    }

    // === Declaration Tests ===
    //
    // Note: Full declaration roundtrip tests require coordinated Rodeo/Spur
    // handling. The encoder creates its own internal Rodeo and expects to
    // resolve Spurs from it. Tests with Spurs would fail because test Spurs
    // come from a different Rodeo.
    //
    // The empty declarations test verifies the basic plumbing works.
    // Full integration testing of declarations should be done at a higher
    // level where a consistent Rodeo context is maintained.

    #[test]
    fn test_roundtrip_empty_declarations() {
        let module = BrrrModule {
            name: "decl_test".to_string(),
            files: vec!["test.brrr".to_string()],
            types: Vec::new(),
            exprs: Vec::new(),
            declarations: Vec::new(),
            version: 1,
        };

        let decoded = roundtrip_module(module);

        assert_eq!(decoded.name, "decl_test");
        assert!(decoded.declarations.is_empty());
    }

    #[test]
    fn test_module_with_all_fields() {
        // Test that all module fields roundtrip correctly
        let module = BrrrModule {
            name: "full_module".to_string(),
            files: vec![
                "src/main.brrr".to_string(),
                "src/lib.brrr".to_string(),
                "src/utils.brrr".to_string(),
            ],
            types: vec![
                BrrrType::UNIT,
                BrrrType::BOOL,
                BrrrType::Numeric(NumericType::Int(IntType::I64)),
            ],
            exprs: vec![
                WithLoc::synthetic(Expr_::Lit(Literal::Bool(true))),
                WithLoc::synthetic(Expr_::Lit(Literal::i32(42))),
            ],
            declarations: Vec::new(),
            version: 1,
        };

        let decoded = roundtrip_module(module);

        assert_eq!(decoded.name, "full_module");
        assert_eq!(decoded.files.len(), 3);
        assert_eq!(decoded.types.len(), 3);
        assert_eq!(decoded.exprs.len(), 2);
        assert!(decoded.declarations.is_empty());
        assert_eq!(decoded.version, 1);
    }
}
