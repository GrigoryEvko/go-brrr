(**
 * BrrrLang.Core.FFI - Interface
 *
 * Foreign Function Interface and Interoperability.
 * Based on brrr_lang_spec_v0.4.tex Part X.
 *
 * ============================================================================
 * OVERVIEW
 * ============================================================================
 *
 * This module provides the complete FFI subsystem for Brrr-Lang, enabling
 * type-safe interoperability with code written in other languages (primarily C).
 * The design follows VeriFFI-style verified FFI patterns as described in
 * synthesis_combined.md Section 9.4.
 *
 * KEY SAFETY PRINCIPLES:
 *
 * 1. UNSAFE CONTEXT REQUIREMENT
 *    All FFI calls require an unsafe context. This follows the specification:
 *      "FFI calls require unsafe context... Inside unsafe, the programmer
 *       asserts memory safety invariants." (brrr_lang_spec_v0.4.tex)
 *    The type system tracks UnsafeFFI effects to ensure this invariant.
 *
 * 2. FFI-SAFE TYPE RESTRICTION
 *    Only types with well-defined C ABI representation can cross FFI boundaries.
 *    The FFISafe set includes (from specification Section "FFI-Safe Types"):
 *      - Fixed-width integers: i8, i16, i32, i64 (NOT i128 or BigInt)
 *      - IEEE 754 floats: f32, f64 (NOT f16 - limited platform support)
 *      - Pointers: Ptr[T] where T is FFI-safe
 *      - Function pointers: FnPtr[T1...Tn -> R]
 *      - C strings: CStr (null-terminated char pointer)
 *      - C-repr structs: Struct with #[repr(C)] attribute
 *
 * 3. REPRESENTATION REQUIREMENTS
 *    Types crossing FFI boundaries must satisfy representation predicates:
 *      - RepNonNull: Pointer must not be null
 *      - RepInitialized: Memory must be fully initialized
 *      - RepAligned: Memory must be properly aligned for the target type
 *      - RepSized: Memory must have sufficient size
 *
 * 4. OWNERSHIP TRANSFER SEMANTICS
 *    FFI contracts explicitly track ownership:
 *      - OTRetained: Caller keeps ownership
 *      - OTTransferred: Ownership moves to callee
 *      - OTBorrowed: Temporary borrow for duration of call
 *      - OTShared: Shared access granted
 *
 * ============================================================================
 * MODULE CONTENTS
 * ============================================================================
 *
 * Provides:
 *   - Calling conventions (C, Rust, System, Fastcall)
 *   - FFI-safe type system with layout guarantees
 *   - Foreign function declarations (extern_fn)
 *   - Memory layout computation with C ABI compliance
 *   - Unsafe effect tracking
 *   - Visibility control for FFI boundaries
 *   - Format string analysis for printf-family functions
 *   - VeriFFI-style contract system (ffi_contract)
 *   - Cross-platform ABI compatibility checking
 *
 * All layout calculations are proven correct with no admits.
 *)
module BrrrFFI

open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrExpressions
open FStar.List.Tot
open FStar.Mul

(* ============================================================================
   VISIBILITY CONTROL FOR FFI BOUNDARIES
   ============================================================================ *)

(** Visibility modifiers control FFI export/import behavior.

    FFIPublic:   Exported across FFI boundary, visible to foreign code.
                 Equivalent to #[no_mangle] pub extern in Rust or
                 __attribute__((visibility("default"))) in GCC/Clang.

    FFIPrivate:  Not exported, internal to current module.
                 The function will not appear in the symbol table.

    FFIInternal: Visible within crate/package but not exported to FFI.
                 Equivalent to pub(crate) in Rust with hidden visibility. *)

type ffi_visibility =
  | FFIPublic   : ffi_visibility
  | FFIPrivate  : ffi_visibility
  | FFIInternal : ffi_visibility

(** String representation for visibility *)
val visibility_to_string : v:ffi_visibility -> string

(** Check if visibility allows FFI export *)
val is_ffi_exported : v:ffi_visibility -> bool

(** Check if visibility allows internal access *)
val is_internally_visible : v:ffi_visibility -> bool

(** Visibility subsumption: v1 <= v2 if v1 is at least as visible as v2 *)
val visibility_subsumes : v1:ffi_visibility -> v2:ffi_visibility -> bool

(** Visibility join: most restrictive common visibility *)
val visibility_join : v1:ffi_visibility -> v2:ffi_visibility -> ffi_visibility

(** Visibility meet: least restrictive common visibility *)
val visibility_meet : v1:ffi_visibility -> v2:ffi_visibility -> ffi_visibility

(** Lemma: visibility_subsumes is reflexive *)
val visibility_subsumes_refl : v:ffi_visibility ->
  Lemma (visibility_subsumes v v = true)
        [SMTPat (visibility_subsumes v v)]

(** Lemma: visibility_subsumes is transitive *)
val visibility_subsumes_trans : v1:ffi_visibility -> v2:ffi_visibility -> v3:ffi_visibility ->
  Lemma (requires visibility_subsumes v1 v2 = true /\ visibility_subsumes v2 v3 = true)
        (ensures visibility_subsumes v1 v3 = true)

(* ============================================================================
   CALLING CONVENTIONS
   ============================================================================ *)

(** Supported calling conventions for FFI.

    CC_C:        Standard C calling convention (cdecl on x86, System V on x64).
                 This is the most portable choice and should be used for all
                 C library interop.

    CC_Rust:     Rust ABI - implementation-defined and unstable.
                 Only use for Rust-to-Rust FFI where both sides use
                 the same Rust compiler version.

    CC_System:   Platform default convention.
                 - Windows: stdcall/Microsoft x64 ABI
                 - Unix: Same as CC_C

    CC_Fastcall: Fastcall convention - first arguments in registers. *)
type calling_convention =
  | CC_C        : calling_convention
  | CC_Rust     : calling_convention
  | CC_System   : calling_convention
  | CC_Fastcall : calling_convention

(** String representation for diagnostics *)
val cc_to_string : cc:calling_convention -> string

(** Check if convention is C-compatible *)
val is_c_compatible : cc:calling_convention -> bool

(* ============================================================================
   FFI-SAFE TYPES
   ============================================================================ *)

(** Types that are safe to pass across FFI boundaries.
    These have well-defined C ABI representation.

    FFIInt:       Fixed-width integers with explicit width and signedness.
    FFIFloat:     IEEE 754 floating point (F32 or F64).
    FFIPtr:       Pointer to FFI-safe type.
    FFIFnPtr:     Function pointer with parameter and return types.
    FFICStr:      C-style null-terminated string.
    FFIVoid:      Void type - only valid as return type or pointer target.
    FFIStruct:    C struct with named fields.
    FFIOpaquePtr: Opaque pointer (void star, i.e., untyped). *)
noeq type ffi_safe_type =
  | FFIInt       : int_width -> signedness -> ffi_safe_type
  | FFIFloat     : float_prec -> ffi_safe_type
  | FFIPtr       : ffi_safe_type -> ffi_safe_type
  | FFIFnPtr     : list ffi_safe_type -> ffi_safe_type -> ffi_safe_type
  | FFICStr      : ffi_safe_type
  | FFIVoid      : ffi_safe_type
  | FFIStruct    : list (string & ffi_safe_type) -> ffi_safe_type
  | FFIOpaquePtr : ffi_safe_type

(** Compute structural depth of FFI type (for termination proofs) *)
val ffi_type_depth : t:ffi_safe_type -> Tot nat (decreases t)

(** Compute depth of a list of FFI types *)
val ffi_type_list_depth : ts:list ffi_safe_type -> Tot nat (decreases ts)

(** Compute depth of a list of struct fields *)
val ffi_field_list_depth : fs:list (string & ffi_safe_type) -> Tot nat (decreases fs)

(** FFI type equality *)
val ffi_type_eq : t1:ffi_safe_type -> t2:ffi_safe_type -> Tot bool (decreases t1)

(** FFI type list equality *)
val ffi_type_list_eq : ts1:list ffi_safe_type -> ts2:list ffi_safe_type -> Tot bool (decreases ts1)

(** FFI field list equality *)
val ffi_field_list_eq : fs1:list (string & ffi_safe_type) -> fs2:list (string & ffi_safe_type)
    -> Tot bool (decreases fs1)

(* ============================================================================
   MEMORY LAYOUT - PLATFORM CONFIGURATION
   ============================================================================ *)

(** Platform configuration for memory layout calculations.
    Captures platform-dependent aspects of memory layout. *)
noeq type platform_config = {
  pc_pointer_size : nat;
  pc_pointer_align: nat;
  pc_long_size    : nat;
  pc_size_t_size  : nat;
}

(** Default platform: LP64 64-bit (Linux, macOS, FreeBSD on x86_64/ARM64) *)
val default_platform_config : platform_config

(** 32-bit platform configuration (ILP32: x86, ARM32, WASM32) *)
val platform_config_32bit : platform_config

(** Windows 64-bit platform configuration (LLP64) *)
val platform_config_windows64 : platform_config

(** Default pointer size (assumes 64-bit platform) *)
val ptr_size : nat

(** Default pointer alignment (assumes 64-bit platform) *)
val ptr_align : nat

(** Platform-aware pointer size *)
val ptr_size_for_platform : cfg:platform_config -> nat

(** Platform-aware pointer alignment *)
val ptr_align_for_platform : cfg:platform_config -> nat

(** Integer width to size in bytes *)
val int_width_size : w:int_width -> nat

(** Platform-aware integer width size (only IBig varies by platform) *)
val int_width_size_for_platform : cfg:platform_config -> w:int_width -> nat

(** Float precision to size in bytes *)
val float_prec_size : p:float_prec -> nat

(* ============================================================================
   POWER OF TWO PROOFS
   ============================================================================ *)

(** Check if n is a power of 2 (or 0, treated as 1) *)
val is_power_of_two : n:nat -> Tot bool (decreases n)

(** Lemma: specific values are powers of 2 *)
val is_power_of_two_1 : unit -> Lemma (is_power_of_two 1 = true)
val is_power_of_two_2 : unit -> Lemma (is_power_of_two 2 = true)
val is_power_of_two_4 : unit -> Lemma (is_power_of_two 4 = true)
val is_power_of_two_8 : unit -> Lemma (is_power_of_two 8 = true)
val is_power_of_two_16 : unit -> Lemma (is_power_of_two 16 = true)

(** Alignment for integer types is always a power of 2 *)
val int_width_align_is_pow2 : w:int_width ->
  Lemma (is_power_of_two (int_width_size w) = true)

(** Alignment for float types is always a power of 2 *)
val float_prec_align_is_pow2 : p:float_prec ->
  Lemma (is_power_of_two (float_prec_size p) = true)

(** Pointer alignment is power of 2 *)
val ptr_align_is_pow2 : unit -> Lemma (is_power_of_two ptr_align = true)

(** Platform-aware pointer alignment lemma *)
val ptr_align_for_platform_is_pow2 : cfg:platform_config ->
  Lemma (requires cfg.pc_pointer_align = 4 \/ cfg.pc_pointer_align = 8)
        (ensures is_power_of_two (ptr_align_for_platform cfg) = true)

(** Platform-aware integer alignment lemma for IBig *)
val int_width_align_for_platform_is_pow2 : cfg:platform_config -> w:int_width ->
  Lemma (requires cfg.pc_pointer_size = 4 \/ cfg.pc_pointer_size = 8)
        (ensures is_power_of_two (int_width_size_for_platform cfg w) = true)

(* ============================================================================
   FFI TYPE SIZE AND ALIGNMENT
   ============================================================================ *)

(** Round up to alignment boundary *)
val align_up : offset:nat -> align:nat -> nat

(** Simple size for non-struct types *)
val ffi_primitive_size : t:ffi_safe_type -> option nat

(** Simple alignment for non-struct types *)
val ffi_primitive_align : t:ffi_safe_type -> option nat

(** Size of FFI type in bytes *)
val ffi_type_size : t:ffi_safe_type -> Tot nat (decreases t)

(** Alignment of FFI type in bytes *)
val ffi_type_align : t:ffi_safe_type -> Tot nat (decreases t)

(** Maximum alignment of struct fields *)
val compute_struct_align_aux : fields:list (string & ffi_safe_type) -> Tot nat (decreases fields)

(** Compute struct size with padding (C layout algorithm) *)
val compute_struct_size_aux :
    fields:list (string & ffi_safe_type) ->
    current_offset:nat ->
    max_align:nat ->
    Tot nat (decreases fields)

(** Wrapper for struct size computation *)
val compute_struct_size : fields:list (string & ffi_safe_type) -> nat

(** Wrapper for struct alignment computation *)
val compute_struct_align : fields:list (string & ffi_safe_type) -> nat

(* ============================================================================
   STRUCT LAYOUT COMPUTATION
   ============================================================================ *)

(** Field layout information: name, byte offset from struct start, size. *)
type field_layout = {
  fl_name   : string;
  fl_offset : nat;
  fl_size   : nat
}

(** Compute C-style struct layout with field offsets *)
val compute_c_layout_aux :
    fields:list (string & ffi_safe_type) ->
    current_offset:nat ->
    Tot (list field_layout) (decreases fields)

(** Compute C-style struct layout *)
val compute_c_layout : fields:list (string & ffi_safe_type) -> list field_layout

(** Alternative return format: list (name, offset, size) *)
val compute_c_layout_tuples : fields:list (string & ffi_safe_type) -> list (string & nat & nat)

(* ============================================================================
   ALIGNMENT PROOFS
   ============================================================================ *)

(** Lemma: max of two powers of 2 is a power of 2 *)
val max_pow2_is_pow2 : a:nat -> b:nat ->
  Lemma (requires is_power_of_two a = true /\ is_power_of_two b = true)
        (ensures is_power_of_two (if a >= b then a else b) = true)

(** Lemma: FFI type alignment is always a power of 2 *)
val ffi_type_align_is_pow2 : t:ffi_safe_type ->
  Lemma (ensures is_power_of_two (ffi_type_align t) = true)
        (decreases t)

(** Lemma: struct alignment is power of 2 *)
val struct_align_is_pow2 : fields:list (string & ffi_safe_type) ->
  Lemma (ensures is_power_of_two (compute_struct_align fields) = true)
        (decreases fields)

(** Lemma: align_up produces offset >= original *)
val align_up_ge : offset:nat -> align:nat ->
  Lemma (align_up offset align >= offset)

(** Lemma: align_up produces aligned result *)
val align_up_aligned : offset:nat -> align:nat{align > 0} ->
  Lemma (align_up offset align % align = 0)

(** Helper: get first field offset, or 0 if empty *)
val first_field_offset : layouts:list field_layout -> nat

(** Lemma: field offsets in layout are non-decreasing *)
val layout_offsets_increasing : fields:list (string & ffi_safe_type) -> offset:nat ->
  Lemma (ensures first_field_offset (compute_c_layout_aux fields offset) >= offset \/
                 Nil? (compute_c_layout_aux fields offset))
  (decreases fields)

(* ============================================================================
   FFI SAFETY CHECKING
   ============================================================================ *)

(** Detailed error type for FFI safety checking. *)
type ffi_safety_error =
  | FFISafeErrNeverType
  | FFISafeErrDynamicType
  | FFISafeErrBigInt
  | FFISafeErrNonCRepr : repr:repr_attr -> ffi_safety_error
  | FFISafeErrNonUnsafeFunction
  | FFISafeErrUnsupportedWrapper : wrapper:wrapper_kind -> ffi_safety_error
  | FFISafeErrNestedField : struct_name:string -> field_name:string ->
                            inner_error:ffi_safety_error -> ffi_safety_error
  | FFISafeErrNestedParam : param_idx:nat -> inner_error:ffi_safety_error -> ffi_safety_error
  | FFISafeErrNestedReturn : inner_error:ffi_safety_error -> ffi_safety_error
  | FFISafeErrUnsupportedType : type_desc:string -> ffi_safety_error

(** Convert FFI safety error to human-readable string *)
val ffi_safety_error_to_string : err:ffi_safety_error -> Tot string (decreases err)

(** FFI safety check result with detailed errors *)
type ffi_safety_result =
  | FFISafeOk : ffi_type:ffi_safe_type -> ffi_safety_result
  | FFISafeErr : error:ffi_safety_error -> ffi_safety_result

(** Detailed FFI safety check with error information *)
val check_ffi_safe : t:brrr_type -> ffi_safety_result

(** Check struct fields for FFI safety with detailed errors *)
val check_fields_ffi_safe : struct_name:string -> fields:list field_type -> ffi_safety_result

(** Check function parameters for FFI safety with detailed errors *)
val check_params_ffi_safe : params:list param_type -> idx:nat -> ffi_safety_result

(** Legacy API: Check if a brrr_type can be used in FFI and convert it *)
val is_ffi_safe : t:brrr_type -> option ffi_safe_type

(** Convert struct fields to FFI fields - legacy API *)
val convert_fields_to_ffi : fields:list field_type -> option (list (string & ffi_safe_type))

(** Convert function parameters to FFI types - legacy API *)
val convert_params_to_ffi : params:list param_type -> option (list ffi_safe_type)

(** Get detailed error when is_ffi_safe returns None *)
val get_ffi_safety_error : t:brrr_type -> option ffi_safety_error

(** Check FFI safety and get either result or formatted error message *)
val check_ffi_safe_with_message : t:brrr_type -> either ffi_safe_type string

(* ============================================================================
   FOREIGN FUNCTION DECLARATION
   ============================================================================ *)

(** Foreign function declaration with visibility control. *)
noeq type extern_fn = {
  fn_name       : string;
  fn_convention : calling_convention;
  fn_params     : list (string & ffi_safe_type);
  fn_return     : ffi_safe_type;
  fn_is_variadic: bool;
  fn_link_name  : option string;
  fn_visibility : ffi_visibility
}

(** Create simple extern function declaration (default: public) *)
val make_extern_fn :
    name:string ->
    params:list (string & ffi_safe_type) ->
    ret:ffi_safe_type ->
    extern_fn

(** Create extern function with specific visibility *)
val make_extern_fn_with_visibility :
    name:string ->
    params:list (string & ffi_safe_type) ->
    ret:ffi_safe_type ->
    vis:ffi_visibility ->
    extern_fn

(** Create private extern function (internal use only) *)
val make_private_extern_fn :
    name:string ->
    params:list (string & ffi_safe_type) ->
    ret:ffi_safe_type ->
    extern_fn

(** Create internal extern function (crate-visible only) *)
val make_internal_extern_fn :
    name:string ->
    params:list (string & ffi_safe_type) ->
    ret:ffi_safe_type ->
    extern_fn

(** Create variadic extern function *)
val make_variadic_extern_fn :
    name:string ->
    params:list (string & ffi_safe_type) ->
    ret:ffi_safe_type ->
    extern_fn

(** Get the actual link name for the function *)
val extern_link_name : fn:extern_fn -> string

(** Check if extern function should be exported across FFI boundary *)
val should_export_extern : fn:extern_fn -> bool

(** Check if extern function is accessible within current crate *)
val is_extern_internally_accessible : fn:extern_fn -> bool

(* ============================================================================
   VISIBILITY VERIFICATION FOR FFI EXPORTS
   ============================================================================ *)

(** FFI export validation error *)
type ffi_visibility_error =
  | VisErrPrivateExport : fn_name:string -> ffi_visibility_error
  | VisErrInternalExport : fn_name:string -> ffi_visibility_error
  | VisErrParamTypeNotPublic : fn_name:string -> param_name:string -> ffi_visibility_error

(** Check that function visibility is valid for FFI export *)
val check_extern_visibility : fn:extern_fn -> exporting:bool -> option ffi_visibility_error

(** Validate a list of extern functions for export *)
val validate_extern_visibility : fns:list extern_fn -> exporting:bool -> list ffi_visibility_error

(* ============================================================================
   UNSAFE EFFECTS AND CHECKING
   ============================================================================ *)

(** Unsafe operation kinds. *)
type unsafe_effect =
  | UnsafeFFI       : unsafe_effect
  | UnsafePtr       : unsafe_effect
  | UnsafeTransmute : unsafe_effect
  | UnsafeAsm       : unsafe_effect
  | UnsafeUnion     : unsafe_effect

(** Unsafe context: tracks what unsafe operations are allowed *)
noeq type unsafe_context = {
  uc_in_unsafe_block : bool;
  uc_in_unsafe_fn    : bool;
  uc_allowed_ops     : list unsafe_effect
}

(** Empty unsafe context (nothing allowed) *)
val no_unsafe : unsafe_context

(** Context inside unsafe block *)
val in_unsafe_block : unsafe_context

(** Context inside unsafe function *)
val in_unsafe_fn : unsafe_context

(** Check if unsafe operation is allowed *)
val is_unsafe_allowed : op:unsafe_effect -> ctx:unsafe_context -> bool

(** Check if FFI call is allowed (must be in unsafe context) *)
val check_ffi_call : fn:extern_fn -> ctx:unsafe_context -> bool

(** Simplified check: FFI call requires unsafe *)
val check_ffi_call_simple : fn:extern_fn -> bool

(* ============================================================================
   FORMAT STRING ANALYSIS FOR PRINTF-FAMILY FUNCTIONS
   ============================================================================ *)

(** Format specifier types *)
type format_specifier =
  | FmtSignedInt      : format_specifier
  | FmtUnsignedInt    : format_specifier
  | FmtHex            : format_specifier
  | FmtOctal          : format_specifier
  | FmtFloat          : format_specifier
  | FmtChar           : format_specifier
  | FmtString         : format_specifier
  | FmtPointer        : format_specifier
  | FmtWriteCount     : format_specifier
  | FmtPercent        : format_specifier

(** Length modifiers affect expected argument type *)
type length_modifier =
  | LenNone   : length_modifier
  | LenHH     : length_modifier
  | LenH      : length_modifier
  | LenL      : length_modifier
  | LenLL     : length_modifier
  | LenBigL   : length_modifier
  | LenZ      : length_modifier
  | LenJ      : length_modifier
  | LenT      : length_modifier

(** Parsed format directive *)
noeq type format_directive = {
  fd_specifier    : format_specifier;
  fd_length       : length_modifier;
  fd_width        : option nat;
  fd_precision    : option nat;
  fd_position     : nat;
}

(** Format string analysis error *)
type format_error =
  | FmtErrInvalidSpecifier : position:nat -> char_code:nat -> format_error
  | FmtErrTooFewArgs : expected:nat -> actual:nat -> format_error
  | FmtErrTooManyArgs : expected:nat -> actual:nat -> format_error
  | FmtErrTypeMismatch : position:nat -> expected:format_specifier ->
                         actual:ffi_safe_type -> format_error
  | FmtErrDangerousN : position:nat -> format_error
  | FmtErrUnboundedString : position:nat -> format_error
  | FmtErrNullFormatString : format_error

(** Convert format specifier to string for diagnostics *)
val format_specifier_to_string : spec:format_specifier -> string

(** Convert format error to string *)
val format_error_to_string : err:format_error -> string

(** Get expected FFI type for format specifier with length modifier *)
val expected_type_for_format :
    spec:format_specifier ->
    len:length_modifier ->
    cfg:platform_config ->
    option ffi_safe_type

(** Check if actual type is compatible with expected format type *)
val type_matches_format : expected:ffi_safe_type -> actual:ffi_safe_type -> bool

(** Format string analysis result *)
noeq type format_analysis_result = {
  far_directives  : list format_directive;
  far_arg_count   : nat;
  far_errors      : list format_error;
  far_warnings    : list format_error;
}

(** Validate format arguments against parsed directives *)
val validate_format_args_aux :
    directives:list format_directive ->
    args:list ffi_safe_type ->
    cfg:platform_config ->
    arg_idx:nat ->
    list format_error

(** Main format validation function for variadic FFI calls *)
val validate_format_call :
    fn_name:string ->
    format_param_idx:nat ->
    directives:list format_directive ->
    variadic_args:list ffi_safe_type ->
    cfg:platform_config ->
    format_analysis_result

(** Identify printf-family functions *)
val is_printf_family : fn_name:string -> bool

(** Get format string parameter index for printf-family functions *)
val get_format_param_index : fn_name:string -> option nat

(* ============================================================================
   TYPE REPRESENTATION ATTRIBUTES
   ============================================================================ *)

(** Extended repr attribute for FFI.
    FReprC:           C-compatible layout
    FReprTransparent: Same layout as single field
    FReprPacked:      No padding between fields
    FReprAlign:       Minimum alignment
    FReprSimd:        SIMD-aligned *)
type ffi_repr_attr =
  | FReprC           : ffi_repr_attr
  | FReprTransparent : ffi_repr_attr
  | FReprPacked      : ffi_repr_attr
  | FReprAlign       : nat -> ffi_repr_attr
  | FReprSimd        : nat -> ffi_repr_attr

(** Convert BrrrTypes repr_attr to ffi_repr_attr *)
val repr_to_ffi_repr : r:repr_attr -> option ffi_repr_attr

(** Check if repr is FFI-compatible *)
val is_repr_ffi_compatible : r:repr_attr -> bool

(* ============================================================================
   POINTER OPERATIONS
   ============================================================================ *)

(** Pointer offset calculation *)
val ptr_offset : base_offset:nat -> index:nat -> element_size:nat -> nat

(** Lemma: pointer offset is commutative in index *)
val ptr_offset_add : base:nat -> i:nat -> j:nat -> size:nat ->
  Lemma (ptr_offset (ptr_offset base i size) j size =
         ptr_offset base (i + j) size)

(** Pointer cast safety *)
type ptr_cast_kind =
  | PtrCastSafe       : ptr_cast_kind
  | PtrCastUpcast     : ptr_cast_kind
  | PtrCastDowncast   : ptr_cast_kind
  | PtrCastReinterpret: ptr_cast_kind

(** Determine pointer cast kind *)
val classify_ptr_cast : from_ty:ffi_safe_type -> to_ty:ffi_safe_type -> ptr_cast_kind

(** Is pointer cast safe without runtime check? *)
val is_ptr_cast_safe : from_ty:ffi_safe_type -> to_ty:ffi_safe_type -> bool

(* ============================================================================
   FFI CALL SIGNATURE VALIDATION
   ============================================================================ *)

(** Helper: take first n elements of a list *)
val firstn : #a:Type -> n:nat -> l:list a -> Tot (list a) (decreases n)

(** Validate that function parameter types match *)
val validate_params : expected:list (string & ffi_safe_type) -> actual:list ffi_safe_type -> bool

(** Validate extern function call *)
val validate_ffi_call : fn:extern_fn -> arg_types:list ffi_safe_type -> bool

(* ============================================================================
   EFFECT ROW FOR FFI
   ============================================================================ *)

(** Effect row for FFI calls *)
val ffi_effect : effect_row

(** Effect row for unsafe FFI calls *)
val unsafe_ffi_effect : effect_row

(** Get effect row for extern function call *)
val extern_fn_effect : fn:extern_fn -> effect_row

(* ============================================================================
   COMMON FFI TYPES
   ============================================================================ *)

(** Standard C types *)
val ffi_c_void : ffi_safe_type
val ffi_c_char : ffi_safe_type
val ffi_c_uchar : ffi_safe_type
val ffi_c_short : ffi_safe_type
val ffi_c_ushort : ffi_safe_type
val ffi_c_int : ffi_safe_type
val ffi_c_uint : ffi_safe_type
val ffi_c_long : ffi_safe_type
val ffi_c_ulong : ffi_safe_type
val ffi_c_longlong : ffi_safe_type
val ffi_c_ulonglong : ffi_safe_type
val ffi_c_float : ffi_safe_type
val ffi_c_double : ffi_safe_type

(** Size types *)
val ffi_size_t : ffi_safe_type
val ffi_ssize_t : ffi_safe_type
val ffi_ptrdiff_t : ffi_safe_type
val ffi_intptr_t : ffi_safe_type
val ffi_uintptr_t : ffi_safe_type

(* ============================================================================
   EXAMPLE FFI DECLARATIONS
   ============================================================================ *)

(** Example: printf declaration *)
val ffi_printf : extern_fn

(** Example: malloc declaration *)
val ffi_malloc : extern_fn

(** Example: free declaration *)
val ffi_free : extern_fn

(* ============================================================================
   VALIDATION LEMMAS
   ============================================================================ *)

(** Lemma: ffi_type_eq is reflexive *)
val ffi_type_eq_refl : t:ffi_safe_type ->
  Lemma (ensures ffi_type_eq t t = true)
        (decreases t)
        [SMTPat (ffi_type_eq t t)]

(** Lemma: ffi_type_list_eq is reflexive *)
val ffi_type_list_eq_refl : ts:list ffi_safe_type ->
  Lemma (ensures ffi_type_list_eq ts ts = true)
        (decreases ts)

(** Lemma: ffi_field_list_eq is reflexive *)
val ffi_field_list_eq_refl : fs:list (string & ffi_safe_type) ->
  Lemma (ensures ffi_field_list_eq fs fs = true)
        (decreases fs)

(** Lemma: empty param list validates against empty arg list *)
val empty_call_succeeds : fn:extern_fn ->
  Lemma (requires fn.fn_is_variadic = false /\ Nil? fn.fn_params)
        (ensures validate_ffi_call fn [] = true)

(* ============================================================================
   STRUCT LAYOUT EXAMPLE AND VERIFICATION
   ============================================================================ *)

(** Example: Point struct fields *)
val point_fields : list (string & ffi_safe_type)

(** Point layout *)
val point_layout : list field_layout

(** Lemma: Point struct has expected size (8 bytes) *)
val point_size_correct : unit ->
  Lemma (compute_struct_size point_fields = 8)

(** Lemma: Point struct has expected alignment (4 bytes) *)
val point_align_correct : unit ->
  Lemma (compute_struct_align point_fields = 4)

(** Example: Padded struct fields *)
val padded_fields : list (string & ffi_safe_type)

(** Verify padded struct size *)
val padded_size_correct : unit ->
  Lemma (compute_struct_size padded_fields = 12)

(* ============================================================================
   FFI CONTRACT SYSTEM - TYPE MAPPINGS
   ============================================================================ *)

(** Language identifier for multi-language FFI *)
type language_id =
  | LangBrrr     : language_id
  | LangC        : language_id
  | LangRust     : language_id
  | LangPython   : language_id
  | LangJava     : language_id
  | LangGo       : language_id

(** Foreign type representation for external languages *)
noeq type foreign_type =
  | ForeignInt8     : foreign_type
  | ForeignInt16    : foreign_type
  | ForeignInt32    : foreign_type
  | ForeignInt64    : foreign_type
  | ForeignUInt8    : foreign_type
  | ForeignUInt16   : foreign_type
  | ForeignUInt32   : foreign_type
  | ForeignUInt64   : foreign_type
  | ForeignFloat    : foreign_type
  | ForeignDouble   : foreign_type
  | ForeignBool     : foreign_type
  | ForeignVoid     : foreign_type
  | ForeignPtr      : foreign_type -> foreign_type
  | ForeignCString  : foreign_type
  | ForeignStruct   : string -> foreign_type
  | ForeignOpaque   : string -> foreign_type

(** IR value placeholder *)
type ir_value = nat

(** Foreign value placeholder *)
type foreign_value = nat

(** Conversion functions between IR and foreign values *)
noeq type conversion_fns = {
  convert_fn   : ir_value -> foreign_value;
  unconvert_fn : foreign_value -> option ir_value
}

(** Type mapping describes how values are transformed when crossing FFI boundaries *)
noeq type type_mapping =
  | TMDirect    : type_mapping
  | TMBoxed     : type_mapping
  | TMConverted : conversion_fns -> type_mapping
  | TMOpaque    : type_mapping

(** Infer type mapping from IR type to foreign type *)
val infer_type_mapping : src:brrr_type -> tgt:foreign_type -> type_mapping

(* ============================================================================
   FFI CONTRACT SYSTEM - REPRESENTATION REQUIREMENTS
   ============================================================================ *)

(** Representation predicate type *)
type rep_predicate = nat

(** Representation requirements for values crossing FFI boundaries *)
type rep_requirement =
  | RepNonNull      : rep_requirement
  | RepInitialized  : rep_requirement
  | RepAligned      : alignment:nat -> rep_requirement
  | RepSized        : min_size:nat -> rep_requirement
  | RepPredicate    : rep_predicate -> rep_requirement

(** Check if requirement implies another *)
val rep_requirement_implies : r1:rep_requirement -> r2:rep_requirement -> bool

(* ============================================================================
   FFI CONTRACT SYSTEM - THREAD SAFETY
   ============================================================================ *)

(** Thread safety requirements for FFI calls *)
type thread_safety_requirement =
  | TSRAnyThread      : thread_safety_requirement
  | TSRSingleThreaded : thread_safety_requirement
  | TSRMainThread     : thread_safety_requirement
  | TSRWithLock       : lock_id -> thread_safety_requirement

(** Thread context *)
noeq type thread_context = {
  tc_is_main_thread : bool;
  tc_held_locks     : list lock_id;
  tc_thread_id      : nat
}

(** Check if thread context satisfies requirement *)
val thread_context_satisfies : ctx:thread_context -> req:thread_safety_requirement -> bool

(* ============================================================================
   FFI CONTRACT SYSTEM - ACCESS PERMISSIONS
   ============================================================================ *)

(** Access permission levels for ownership requirements *)
type access_permission =
  | APNone      : access_permission
  | APRead      : access_permission
  | APWrite     : access_permission
  | APOwned     : access_permission

(** Permission level *)
val permission_level : p:access_permission -> nat

(** Check if actual permission satisfies required permission *)
val permission_satisfies : actual:access_permission -> required:access_permission -> bool

(* ============================================================================
   FFI CONTRACT SYSTEM - PRECONDITIONS
   ============================================================================ *)

(** Constraint expression placeholder *)
type constraint_expr = nat

(** FFI precondition captures all requirements that must hold before the call *)
noeq type ffi_precondition = {
  pre_rep_requirements       : list (var_id & rep_requirement);
  pre_ownership_requirements : list (var_id & access_permission);
  pre_value_constraints      : list (var_id & constraint_expr);
  pre_thread_requirements    : option thread_safety_requirement
}

(** Empty precondition - no requirements *)
val empty_precondition : ffi_precondition

(** Add representation requirement to precondition *)
val add_rep_requirement : pre:ffi_precondition -> v:var_id -> r:rep_requirement -> ffi_precondition

(** Add ownership requirement to precondition *)
val add_ownership_requirement : pre:ffi_precondition -> v:var_id -> p:access_permission -> ffi_precondition

(* ============================================================================
   FFI CONTRACT SYSTEM - MEMORY EFFECTS
   ============================================================================ *)

(** Address type for memory effect specification *)
type address = nat

(** Memory effect specification describes what the callee may do to memory *)
type memory_effect_spec =
  | MEUnchanged     : memory_effect_spec
  | MEModifiedOnly  : list address -> memory_effect_spec
  | MEMayAllocate   : memory_effect_spec
  | MEMayFree       : list address -> memory_effect_spec
  | MEArbitrary     : memory_effect_spec

(** Check if effect spec is pure (no memory effects) *)
val is_pure_effect : e:memory_effect_spec -> bool

(* ============================================================================
   FFI CONTRACT SYSTEM - OWNERSHIP TRANSFER
   ============================================================================ *)

(** Lifetime bound for borrowed references *)
type lifetime_bound =
  | LBStatic : lifetime_bound
  | LBScoped : nat -> lifetime_bound
  | LBNamed  : string -> lifetime_bound

(** Ownership transfer specifies how ownership changes during FFI call *)
type ownership_transfer =
  | OTRetained    : ownership_transfer
  | OTTransferred : ownership_transfer
  | OTBorrowed    : lifetime_bound -> ownership_transfer
  | OTShared      : ownership_transfer

(** Check if ownership transfer is safe *)
val ownership_transfer_safe : ot:ownership_transfer -> has_lifetime:bool -> bool

(* ============================================================================
   FFI CONTRACT SYSTEM - ERROR BEHAVIOR
   ============================================================================ *)

(** Error behavior describes how errors are reported across the boundary *)
noeq type error_behavior =
  | EBException  : brrr_type -> error_behavior
  | EBReturnCode : ir_value -> error_behavior
  | EBSetErrno   : error_behavior
  | EBAbort      : error_behavior
  | EBUndefined  : error_behavior

(* ============================================================================
   FFI CONTRACT SYSTEM - POSTCONDITIONS
   ============================================================================ *)

(** FFI postcondition captures guarantees the callee provides *)
noeq type ffi_postcondition = {
  post_return_rep        : rep_requirement;
  post_memory_effects    : memory_effect_spec;
  post_ownership_effects : list (var_id & ownership_transfer);
  post_error_conditions  : list (constraint_expr & error_behavior);
  post_may_trigger_gc    : bool
}

(** Default postcondition - conservative assumptions *)
val default_postcondition : ffi_postcondition

(** Pure postcondition - no side effects *)
val pure_postcondition : ffi_postcondition

(* ============================================================================
   FFI CONTRACT SYSTEM - OWNERSHIP SPEC
   ============================================================================ *)

(** Ownership specification for all parameters *)
noeq type ownership_spec = {
  os_params : list (var_id & ownership_transfer);
  os_return : ownership_transfer
}

(** Default ownership spec - all retained *)
val default_ownership_spec : ownership_spec

(* ============================================================================
   FFI CONTRACT SYSTEM - FFI CONTRACT
   ============================================================================ *)

(** FFI Contract fully specifies the requirements for a cross-language call *)
noeq type ffi_contract = {
  fc_foreign_function  : string;
  fc_source_language   : language_id;
  fc_target_language   : language_id;
  fc_param_types       : list (brrr_type & foreign_type & type_mapping);
  fc_return_type       : brrr_type & foreign_type & type_mapping;
  fc_precondition      : ffi_precondition;
  fc_postcondition     : ffi_postcondition;
  fc_ownership         : ownership_spec;
  fc_effect_bounds     : effect_row
}

(** Create basic FFI contract with defaults *)
val make_basic_contract :
    name:string ->
    params:list (brrr_type & foreign_type) ->
    ret:brrr_type & foreign_type ->
    ffi_contract

(* ============================================================================
   FFI CONTRACT ANNOTATIONS
   ============================================================================ *)

(** Annotations for refining auto-generated contracts *)
type ffi_annotation =
  | AnnNonnull      : var_id -> ffi_annotation
  | AnnNullable     : var_id -> ffi_annotation
  | AnnOwned        : var_id -> ffi_annotation
  | AnnBorrowed     : var_id -> ffi_annotation
  | AnnOut          : var_id -> ffi_annotation
  | AnnInOut        : var_id -> ffi_annotation
  | AnnArraySize    : var_id -> nat -> ffi_annotation
  | AnnBufferSize   : var_id -> var_id -> ffi_annotation
  | AnnMayAllocate  : ffi_annotation
  | AnnMayFree      : ffi_annotation
  | AnnPure         : ffi_annotation
  | AnnThreadSafe   : ffi_annotation

(** Apply annotation to contract *)
val apply_annotation : c:ffi_contract -> ann:ffi_annotation -> ffi_contract

(** Apply list of annotations to contract *)
val refine_contract_with_annotations : c:ffi_contract -> anns:list ffi_annotation -> ffi_contract

(* ============================================================================
   FFI VIOLATION TYPES
   ============================================================================ *)

(** Node ID placeholder for violation locations *)
type violation_node_id = nat

(** FFI violation describes a contract violation detected during verification *)
noeq type ffi_violation =
  | VRepViolation
      : param:var_id
      -> expected:rep_requirement
      -> actual:nat
      -> ffi_violation
  | VOwnershipViolation
      : param:var_id
      -> required:access_permission
      -> actual:access_permission
      -> ffi_violation
  | VTypeMismatch
      : expected:foreign_type
      -> actual:brrr_type
      -> ffi_violation
  | VNullViolation
      : param:var_id
      -> ffi_violation
  | VUninitializedViolation
      : param:var_id
      -> ffi_violation
  | VThreadViolation
      : required:thread_safety_requirement
      -> actual:thread_context
      -> ffi_violation
  | VMissingContract
      : function_name:string
      -> ffi_violation
  | VConversionFailure
      : param:var_id
      -> from_type:brrr_type
      -> to_type:foreign_type
      -> ffi_violation

(** Convert violation to string for error reporting *)
val violation_to_string : v:ffi_violation -> string

(* ============================================================================
   ABSTRACT STATE FOR VERIFICATION
   ============================================================================ *)

(** Abstract value representation for verification *)
noeq type abs_value = {
  av_may_be_null        : bool;
  av_may_be_uninitialized : bool;
  av_known_alignment    : option nat;
  av_known_size         : option nat;
  av_permission         : access_permission
}

(** Create unknown abstract value *)
val unknown_abs_value : abs_value

(** Create concrete abstract value (fully known) *)
val concrete_abs_value : align:nat -> size:nat -> perm:access_permission -> abs_value

(** Abstract state: mapping from variables to abstract values *)
type abs_state = list (var_id & abs_value)

(** Lookup abstract value for variable *)
val lookup_abs_value : s:abs_state -> v:var_id -> option abs_value

(** Empty abstract state *)
val empty_abs_state : abs_state

(* ============================================================================
   CONTRACT VERIFICATION
   ============================================================================ *)

(** Check representation requirement against abstract value *)
val check_rep_requirement : av:abs_value -> req:rep_requirement -> option string

(** Check all representation requirements in precondition *)
val check_all_rep_requirements : state:abs_state -> reqs:list (var_id & rep_requirement)
    -> list ffi_violation

(** Check all ownership requirements in precondition *)
val check_all_ownership_requirements : state:abs_state -> reqs:list (var_id & access_permission)
    -> list ffi_violation

(** Check thread safety requirement *)
val check_thread_requirement : ctx:thread_context -> req:option thread_safety_requirement
    -> list ffi_violation

(** Verification result type *)
noeq type verification_result =
  | VROk     : abs_state -> verification_result
  | VRError  : list ffi_violation -> verification_result

(** Apply postcondition to compute post-state *)
val apply_postcondition : state:abs_state -> post:ffi_postcondition -> abs_state

(** Unsafe context violation *)
type unsafe_context_violation =
  | UCVNotInUnsafe : function_name:string -> unsafe_context_violation
  | UCVMissingEffect : function_name:string -> required:unsafe_effect -> unsafe_context_violation

(** Check if unsafe context permits FFI call *)
val check_unsafe_context_for_ffi : ctx:unsafe_context -> fn_name:string
    -> option unsafe_context_violation

(** Main verification function: verify FFI call against contract *)
val verify_ffi_call :
    call_site:violation_node_id ->
    contract:ffi_contract ->
    state:abs_state ->
    thread_ctx:thread_context ->
    unsafe_ctx:unsafe_context ->
    verification_result

(** Simplified verification without thread context *)
val verify_ffi_call_simple :
    contract:ffi_contract ->
    state:abs_state ->
    unsafe_ctx:unsafe_context ->
    verification_result

(** Verification assuming we are in an unsafe block *)
val verify_ffi_call_in_unsafe :
    contract:ffi_contract ->
    state:abs_state ->
    verification_result

(* ============================================================================
   CONTRACT DATABASE AND BATCH VERIFICATION
   ============================================================================ *)

(** Contract database: maps function names to contracts *)
type contract_db = list (string & ffi_contract)

(** Lookup contract for function *)
val lookup_contract : db:contract_db -> name:string -> option ffi_contract

(** FFI call site representation *)
noeq type ffi_call_site = {
  fcs_node_id   : violation_node_id;
  fcs_func_name : string;
  fcs_state     : abs_state
}

(** Verify all FFI calls in a list against contract database *)
val verify_all_ffi_calls :
    db:contract_db ->
    calls:list ffi_call_site ->
    thread_ctx:thread_context ->
    unsafe_ctx:unsafe_context ->
    list (violation_node_id & ffi_violation)

(* ============================================================================
   EXAMPLE FFI CONTRACTS
   ============================================================================ *)

(** Contract for malloc *)
val contract_malloc : ffi_contract

(** Contract for free *)
val contract_free : ffi_contract

(** Contract for strlen *)
val contract_strlen : ffi_contract

(* ============================================================================
   VERIFICATION LEMMAS
   ============================================================================ *)

(** Lemma: empty precondition always passes *)
val empty_precondition_passes : state:abs_state ->
  Lemma (check_all_rep_requirements state [] = [] /\
         check_all_ownership_requirements state [] = [])

(** Lemma: permission_satisfies is reflexive *)
val permission_satisfies_refl : p:access_permission ->
  Lemma (permission_satisfies p p = true)
        [SMTPat (permission_satisfies p p)]

(** Lemma: permission_satisfies is transitive *)
val permission_satisfies_trans : p1:access_permission -> p2:access_permission ->
                                 p3:access_permission ->
  Lemma (requires permission_satisfies p1 p2 = true /\
                  permission_satisfies p2 p3 = true)
        (ensures permission_satisfies p1 p3 = true)

(** Lemma: owned permission satisfies all permissions *)
val owned_satisfies_all : p:access_permission ->
  Lemma (permission_satisfies APOwned p = true)

(** Lemma: concrete abstract value with proper alignment satisfies aligned requirement *)
val concrete_satisfies_aligned : align:nat -> size:nat -> perm:access_permission ->
  Lemma (requires align > 0)
        (ensures check_rep_requirement (concrete_abs_value align size perm)
                                       (RepAligned align) = None)

(** Lemma: concrete abstract value with proper size satisfies sized requirement *)
val concrete_satisfies_sized : align:nat -> size:nat -> perm:access_permission ->
  Lemma (check_rep_requirement (concrete_abs_value align size perm)
                               (RepSized size) = None)

(* ============================================================================
   ABI COMPATIBILITY CHECKING - ENDIANNESS
   ============================================================================ *)

(** Endianness affects multi-byte value interpretation *)
type endianness =
  | BigEndian    : endianness
  | LittleEndian : endianness

(** Convert endianness to string *)
val endianness_to_string : e:endianness -> string

(** Check if byte swap is needed between two endiannesses *)
val needs_byte_swap : source:endianness -> target:endianness -> bool

(* ============================================================================
   ABI COMPATIBILITY CHECKING - ARCHITECTURE
   ============================================================================ *)

(** CPU architecture identifier *)
type arch =
  | Arch_x86     : arch
  | Arch_x86_64  : arch
  | Arch_ARM32   : arch
  | Arch_ARM64   : arch
  | Arch_RISCV32 : arch
  | Arch_RISCV64 : arch
  | Arch_WASM32  : arch
  | Arch_WASM64  : arch

(** Convert architecture to string *)
val arch_to_string : a:arch -> string

(** Get pointer size for architecture (in bytes) *)
val arch_pointer_size : a:arch -> nat

(** Get default endianness for architecture *)
val arch_default_endianness : a:arch -> endianness

(* ============================================================================
   ABI COMPATIBILITY CHECKING - OPERATING SYSTEM
   ============================================================================ *)

(** Operating system identifier *)
type target_os =
  | OS_Linux   : target_os
  | OS_Windows : target_os
  | OS_MacOS   : target_os
  | OS_FreeBSD : target_os
  | OS_iOS     : target_os
  | OS_Android : target_os
  | OS_WASI    : target_os
  | OS_None    : target_os

(** Convert OS to string *)
val os_to_string : o:target_os -> string

(** Is this OS POSIX-like? *)
val is_posix_like : o:target_os -> bool

(* ============================================================================
   ABI COMPATIBILITY CHECKING - PACKING MODE
   ============================================================================ *)

(** Struct packing mode affects field alignment and padding *)
type packing_mode =
  | PackDefault  : packing_mode
  | PackPacked   : packing_mode
  | PackAlign    : alignment:nat -> packing_mode
  | PackExplicit : packing_mode

(** Convert packing mode to string *)
val packing_mode_to_string : p:packing_mode -> string

(* ============================================================================
   ABI COMPATIBILITY CHECKING - LAYOUT INFO
   ============================================================================ *)

(** Physical memory layout information for a type *)
noeq type layout_info = {
  li_size      : nat;
  li_alignment : nat;
  li_endianness: endianness
}

(** Create layout info *)
val make_layout_info : size:nat -> align:nat -> endian:endianness -> layout_info

(** Check if layout_info values are compatible *)
val layout_info_compatible : l1:layout_info -> l2:layout_info -> bool

(** Check if layouts are exactly equal *)
val layout_info_eq : l1:layout_info -> l2:layout_info -> bool

(* ============================================================================
   ABI COMPATIBILITY CHECKING - TARGET ABI
   ============================================================================ *)

(** Complete target ABI specification *)
noeq type target_abi = {
  abi_arch           : arch;
  abi_os             : target_os;
  abi_endianness     : endianness;
  abi_pointer_size   : nat;
  abi_i8_size        : nat;
  abi_i16_size       : nat;
  abi_i32_size       : nat;
  abi_i64_size       : nat;
  abi_i128_size      : nat;
  abi_long_size      : nat;
  abi_size_t_size    : nat;
  abi_f32_size       : nat;
  abi_f64_size       : nat;
  abi_max_align      : nat;
  abi_packing        : packing_mode;
  abi_calling_conv   : calling_convention
}

(** Get ABI name for display *)
val abi_to_string : abi:target_abi -> string

(** Get integer width size for this ABI *)
val abi_int_width_size : abi:target_abi -> w:int_width -> nat

(** Get float precision size for this ABI *)
val abi_float_prec_size : abi:target_abi -> p:float_prec -> nat

(* ============================================================================
   PLATFORM DATABASE
   ============================================================================ *)

(** Linux x86_64 (LP64 ABI - System V AMD64 ABI) *)
val abi_linux_x86_64 : target_abi

(** Linux x86 (ILP32 ABI) *)
val abi_linux_x86 : target_abi

(** Windows x86_64 (LLP64 ABI - Microsoft x64) *)
val abi_windows_x86_64 : target_abi

(** Windows x86 (ILP32 ABI) *)
val abi_windows_x86 : target_abi

(** macOS x86_64 (LP64 ABI - System V AMD64 ABI variant) *)
val abi_macos_x86_64 : target_abi

(** macOS ARM64 (LP64 ABI - Apple Silicon) *)
val abi_macos_arm64 : target_abi

(** Linux ARM64 (LP64 ABI - AAPCS64) *)
val abi_linux_arm64 : target_abi

(** Linux ARM32 (ILP32 ABI - AAPCS) *)
val abi_linux_arm32 : target_abi

(** WebAssembly 32-bit (wasm32-unknown-unknown) *)
val abi_wasm32 : target_abi

(** Android ARM64 (LP64 ABI) *)
val abi_android_arm64 : target_abi

(** iOS ARM64 (LP64 ABI) *)
val abi_ios_arm64 : target_abi

(** Get predefined ABI for a target triple *)
val get_predefined_abi : a:arch -> o:target_os -> option target_abi

(* ============================================================================
   ABI MISMATCH TYPES
   ============================================================================ *)

(** ABI mismatch diagnostic information *)
type abi_mismatch =
  | SizeMismatch
      : expected:nat
      -> actual:nat
      -> abi_mismatch
  | AlignmentMismatch
      : field:string
      -> expected:nat
      -> actual:nat
      -> abi_mismatch
  | OffsetMismatch
      : field:string
      -> expected:nat
      -> actual:nat
      -> abi_mismatch
  | TypeWidthMismatch
      : field:string
      -> expected:nat
      -> actual:nat
      -> abi_mismatch
  | EndiannessMismatch
      : field:string
      -> source:endianness
      -> target:endianness
      -> abi_mismatch
  | FieldCountMismatch
      : expected:nat
      -> actual:nat
      -> abi_mismatch
  | FieldNameMismatch
      : index:nat
      -> expected:string
      -> actual:string
      -> abi_mismatch

(** Convert ABI mismatch to human-readable string *)
val abi_mismatch_to_string : m:abi_mismatch -> string

(** Severity level for ABI mismatches *)
type mismatch_severity =
  | SeverityCritical : mismatch_severity
  | SeverityHigh     : mismatch_severity
  | SeverityMedium   : mismatch_severity
  | SeverityLow      : mismatch_severity

(** Get severity for an ABI mismatch *)
noeq type ir_field = {
  irf_name   : string;
  irf_type   : ffi_safe_type;
  irf_offset : nat;
  irf_size   : nat;
  irf_align  : nat
}

(** IR struct with full layout metadata *)
noeq type ir_struct = {
  irs_name   : string;
  irs_fields : list ir_field;
  irs_layout : layout_info;
  irs_abi    : target_abi
}

(* ============================================================================
   ABI-AWARE LAYOUT COMPUTATION
   ============================================================================ *)

(** Get size of FFI type under a specific ABI *)
val ffi_type_size_abi : abi:target_abi -> t:ffi_safe_type -> Tot nat (decreases t)

(** Get alignment of FFI type under a specific ABI *)
val ffi_type_align_abi : abi:target_abi -> t:ffi_safe_type -> Tot nat (decreases t)

(** Compute struct alignment for given ABI *)
val compute_struct_align_abi : abi:target_abi -> fields:list (string & ffi_safe_type)
    -> Tot nat (decreases fields)

(** Compute struct size with ABI-specific padding *)
val compute_struct_size_abi : abi:target_abi -> fields:list (string & ffi_safe_type)
    -> Tot nat (decreases fields)

(** Auxiliary function for struct size computation with accumulator *)
val compute_struct_size_abi_aux :
    abi:target_abi ->
    fields:list (string & ffi_safe_type) ->
    current_offset:nat ->
    max_align:nat ->
    Tot nat (decreases fields)

(** Compute full field layout for struct under given ABI *)
val compute_layout_abi_aux :
    abi:target_abi ->
    fields:list (string & ffi_safe_type) ->
    current_offset:nat ->
    Tot (list ir_field) (decreases fields)

(** Compute struct with full layout under given ABI *)
val compute_struct_layout_for_abi :
    name:string ->
    fields:list (string & ffi_safe_type) ->
    abi:target_abi ->
    ir_struct

(* ============================================================================
   ABI COMPATIBILITY CHECKING
   ============================================================================ *)

(** Compare two field lists for mismatches *)
val compare_fields :
    source_fields:list ir_field ->
    target_fields:list ir_field ->
    source_endian:endianness ->
    target_endian:endianness ->
    list abi_mismatch

(** Main ABI compatibility check function *)
val check_abi_compatibility : source_struct:ir_struct -> target_struct:ir_struct -> list abi_mismatch

(** Check if two structs are ABI-compatible *)
val is_abi_compatible : source:ir_struct -> target:ir_struct -> bool

(** Check compatibility and return critical mismatches only *)
val check_critical_abi_mismatches : source_struct:ir_struct -> target_struct:ir_struct
    -> list abi_mismatch

(* ============================================================================
   CROSS-PLATFORM ABI CHECKING
   ============================================================================ *)

(** Check struct compatibility between two ABIs *)
val check_cross_platform_compatibility :
    name:string ->
    fields:list (string & ffi_safe_type) ->
    source_abi:target_abi ->
    target_abi:target_abi ->
    list abi_mismatch

(** Check struct against multiple target ABIs and collect all mismatches *)
val check_against_all_targets :
    name:string ->
    fields:list (string & ffi_safe_type) ->
    source_abi:target_abi ->
    target_abis:list target_abi ->
    list (target_abi & list abi_mismatch)

(** Common target ABIs for portable code verification *)
val common_target_abis : list target_abi

(** Check portability across common platforms *)
val check_portability :
    name:string ->
    fields:list (string & ffi_safe_type) ->
    source_abi:target_abi ->
    list (target_abi & list abi_mismatch)

(* ============================================================================
   BYTE ORDER CONVERSION TRACKING
   ============================================================================ *)

(** Byte order conversion requirement *)
type byte_order_conversion =
  | BOCNone     : byte_order_conversion
  | BOCSwap16   : byte_order_conversion
  | BOCSwap32   : byte_order_conversion
  | BOCSwap64   : byte_order_conversion
  | BOCSwap128  : byte_order_conversion

(** Get required byte order conversion for a field *)
val get_byte_order_conversion :
    source_endian:endianness ->
    target_endian:endianness ->
    field_size:nat ->
    byte_order_conversion

(** Generate byte order conversion requirements for struct *)
val get_struct_byte_conversions :
    source_endian:endianness ->
    target_endian:endianness ->
    fields:list ir_field ->
    list (string & byte_order_conversion)

(* ============================================================================
   ABI COMPATIBILITY PROOFS
   ============================================================================ *)

(** Lemma: struct layout under same ABI is consistent *)
val same_abi_same_layout : abi:target_abi -> name:string -> fields:list (string & ffi_safe_type) ->
  Lemma (let s1 = compute_struct_layout_for_abi name fields abi in
         let s2 = compute_struct_layout_for_abi name fields abi in
         s1.irs_layout.li_size = s2.irs_layout.li_size)

(** Lemma: is_abi_compatible is reflexive *)
val abi_compatible_reflexive : s:ir_struct ->
  Lemma (is_abi_compatible s s = true)

(** Lemma: empty struct has size 0 (or minimum alignment) on any ABI *)
val empty_struct_zero_size : abi:target_abi ->
  Lemma (compute_struct_size_abi abi [] = 1)

(** Lemma: packed struct has no padding between fields *)
val packed_struct_no_padding : name:string ->
                               f1_name:string -> f1_type:ffi_safe_type ->
                               f2_name:string -> f2_type:ffi_safe_type ->
                               abi:target_abi ->
  Lemma (requires abi.abi_packing = PackPacked)
        (ensures (let fields = [(f1_name, f1_type); (f2_name, f2_type)] in
                  let s = compute_struct_layout_for_abi name fields abi in
                  match s.irs_fields with
                  | [f1; f2] -> f2.irf_offset = f1.irf_offset + f1.irf_size
                  | _ -> False))

(* ============================================================================
   EXAMPLE: WINDOWS VS LINUX 'LONG' SIZE DIFFERENCE
   ============================================================================ *)

(** Example struct that exhibits the Windows/Linux long mismatch *)
val example_data_fields : list (string & ffi_safe_type)

(** Verify the example struct has same layout on Windows and Linux *)
val example_struct_portable : unit ->
  Lemma (let win = compute_struct_layout_for_abi "Data" example_data_fields abi_windows_x86_64 in
         let lin = compute_struct_layout_for_abi "Data" example_data_fields abi_linux_x86_64 in
         win.irs_layout.li_size = lin.irs_layout.li_size)

(* ============================================================================
   FFI GUARD GENERATION FROM ABI CHECKS
   ============================================================================ *)

(** Guard type for runtime ABI verification *)
type abi_guard =
  | GuardSizeOf
      : type_name:string
      -> expected:nat
      -> abi_guard
  | GuardAlignOf
      : type_name:string
      -> expected:nat
      -> abi_guard
  | GuardOffsetOf
      : type_name:string
      -> field_name:string
      -> expected:nat
      -> abi_guard

(** Generate guards for a struct layout *)
val generate_field_guards : struct_name:string -> fields:list ir_field -> list abi_guard

(** Generate all guards for a struct *)
val generate_struct_guards : s:ir_struct -> list abi_guard

(** Convert guard to C static_assert string *)
val guard_to_c_assert : g:abi_guard -> string
val mismatch_severity : m:abi_mismatch -> mismatch_severity

(* ============================================================================
   IR STRUCT WITH LAYOUT METADATA
   ============================================================================ *)

(** Field with explicit offset information *)
