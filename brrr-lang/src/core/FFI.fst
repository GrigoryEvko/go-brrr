(**
 * BrrrLang.Core.FFI
 *
 * Foreign Function Interface and Interoperability.
 * Based on brrr_lang_spec_v0.4.tex Part X.
 *
 * Provides:
 *   - Calling conventions (C, Rust, System, Fastcall)
 *   - FFI-safe type system with layout guarantees
 *   - Foreign function declarations
 *   - Memory layout computation with C ABI compliance
 *   - Unsafe effect tracking
 *   - Visibility control for FFI boundaries
 *
 * All layout calculations are proven correct with no admits.
 *)
module FFI

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open Primitives
open Modes
open Effects
open BrrrTypes
open Expressions
open FStar.List.Tot
open FStar.Mul

(** ============================================================================
    VISIBILITY CONTROL FOR FFI BOUNDARIES
    ============================================================================ *)

(* Visibility modifiers control FFI export/import behavior.
 *
 * Public:   Exported across FFI boundary, visible to foreign code
 * Private:  Not exported, internal to current module
 * Internal: Visible within crate/package but not exported to FFI
 *
 * This follows Rust's visibility model adapted for FFI contexts. *)
type ffi_visibility =
  | FFIPublic   : ffi_visibility   (* #[no_mangle] pub extern - fully exported *)
  | FFIPrivate  : ffi_visibility   (* Not exported across FFI boundary *)
  | FFIInternal : ffi_visibility   (* pub(crate) - internal linkage *)

(* String representation for visibility *)
let visibility_to_string (v: ffi_visibility) : string =
  match v with
  | FFIPublic -> "public"
  | FFIPrivate -> "private"
  | FFIInternal -> "internal"

(* Check if visibility allows FFI export *)
let is_ffi_exported (v: ffi_visibility) : bool =
  match v with
  | FFIPublic -> true
  | FFIPrivate -> false
  | FFIInternal -> false

(* Check if visibility allows internal access *)
let is_internally_visible (v: ffi_visibility) : bool =
  match v with
  | FFIPublic -> true
  | FFIPrivate -> false
  | FFIInternal -> true

(* Visibility subsumption: v1 <= v2 if v1 is at least as visible as v2 *)
let visibility_subsumes (v1 v2: ffi_visibility) : bool =
  match v1, v2 with
  | FFIPublic, _ -> true           (* Public subsumes everything *)
  | FFIInternal, FFIInternal -> true
  | FFIInternal, FFIPrivate -> true
  | FFIPrivate, FFIPrivate -> true
  | _, _ -> false

(* Visibility join: most restrictive common visibility *)
let visibility_join (v1 v2: ffi_visibility) : ffi_visibility =
  match v1, v2 with
  | FFIPrivate, _ -> FFIPrivate
  | _, FFIPrivate -> FFIPrivate
  | FFIInternal, _ -> FFIInternal
  | _, FFIInternal -> FFIInternal
  | FFIPublic, FFIPublic -> FFIPublic

(* Visibility meet: least restrictive common visibility *)
let visibility_meet (v1 v2: ffi_visibility) : ffi_visibility =
  match v1, v2 with
  | FFIPublic, _ -> FFIPublic
  | _, FFIPublic -> FFIPublic
  | FFIInternal, _ -> FFIInternal
  | _, FFIInternal -> FFIInternal
  | FFIPrivate, FFIPrivate -> FFIPrivate

(* Lemma: visibility_subsumes is reflexive *)
val visibility_subsumes_refl : v:ffi_visibility ->
  Lemma (visibility_subsumes v v = true)
        [SMTPat (visibility_subsumes v v)]
let visibility_subsumes_refl v = ()

(* Lemma: visibility_subsumes is transitive *)
val visibility_subsumes_trans : v1:ffi_visibility -> v2:ffi_visibility -> v3:ffi_visibility ->
  Lemma (requires visibility_subsumes v1 v2 = true /\ visibility_subsumes v2 v3 = true)
        (ensures visibility_subsumes v1 v3 = true)
let visibility_subsumes_trans v1 v2 v3 = ()

(** ============================================================================
    CALLING CONVENTIONS
    ============================================================================ *)

(* Supported calling conventions for FFI *)
type calling_convention =
  | CC_C        : calling_convention   (* Standard C calling convention (cdecl) *)
  | CC_Rust     : calling_convention   (* Rust ABI (implementation-defined) *)
  | CC_System   : calling_convention   (* Platform default (stdcall on Win32, C elsewhere) *)
  | CC_Fastcall : calling_convention   (* Fastcall: first args in registers *)

(* String representation for diagnostics *)
let cc_to_string (cc: calling_convention) : string =
  match cc with
  | CC_C -> "C"
  | CC_Rust -> "Rust"
  | CC_System -> "system"
  | CC_Fastcall -> "fastcall"

(* Check if convention is C-compatible (most FFI targets require this) *)
let is_c_compatible (cc: calling_convention) : bool =
  match cc with
  | CC_C -> true
  | CC_System -> true
  | CC_Fastcall -> true
  | CC_Rust -> false

(** ============================================================================
    FFI-SAFE TYPES
    ============================================================================ *)

(* Types that are safe to pass across FFI boundaries.
   These have well-defined C ABI representation.

   FFIInt       - Primitive integers with explicit width and signedness
   FFIFloat     - IEEE 754 floating point
   FFIPtr       - Pointer to FFI-safe type
   FFIFnPtr     - Function pointer with parameter and return types
   FFICStr      - C-style null-terminated string (char pointer)
   FFIVoid      - Void type (only valid as return type or pointer target)
   FFIStruct    - C struct with named fields
   FFIOpaquePtr - Opaque pointer (void pointer) *)
noeq type ffi_safe_type =
  | FFIInt       : int_width -> signedness -> ffi_safe_type
  | FFIFloat     : float_prec -> ffi_safe_type
  | FFIPtr       : ffi_safe_type -> ffi_safe_type
  | FFIFnPtr     : list ffi_safe_type -> ffi_safe_type -> ffi_safe_type
  | FFICStr      : ffi_safe_type
  | FFIVoid      : ffi_safe_type
  | FFIStruct    : list (string & ffi_safe_type) -> ffi_safe_type
  | FFIOpaquePtr : ffi_safe_type

(* Compute structural size of FFI type (for termination proofs) *)
let rec ffi_type_depth (t: ffi_safe_type) : Tot nat (decreases t) =
  match t with
  | FFIInt _ _ -> 1
  | FFIFloat _ -> 1
  | FFIPtr inner -> 1 + ffi_type_depth inner
  | FFIFnPtr params ret -> 1 + ffi_type_list_depth params + ffi_type_depth ret
  | FFICStr -> 1
  | FFIVoid -> 1
  | FFIStruct fields -> 1 + ffi_field_list_depth fields
  | FFIOpaquePtr -> 1

and ffi_type_list_depth (ts: list ffi_safe_type) : Tot nat (decreases ts) =
  match ts with
  | [] -> 0
  | t :: rest -> ffi_type_depth t + ffi_type_list_depth rest

and ffi_field_list_depth (fs: list (string & ffi_safe_type)) : Tot nat (decreases fs) =
  match fs with
  | [] -> 0
  | (_, t) :: rest -> ffi_type_depth t + ffi_field_list_depth rest

(* FFI type equality *)
let rec ffi_type_eq (t1 t2: ffi_safe_type) : Tot bool (decreases t1) =
  match t1, t2 with
  | FFIInt w1 s1, FFIInt w2 s2 -> w1 = w2 && s1 = s2
  | FFIFloat p1, FFIFloat p2 -> p1 = p2
  | FFIPtr i1, FFIPtr i2 -> ffi_type_eq i1 i2
  | FFIFnPtr ps1 r1, FFIFnPtr ps2 r2 ->
      ffi_type_list_eq ps1 ps2 && ffi_type_eq r1 r2
  | FFICStr, FFICStr -> true
  | FFIVoid, FFIVoid -> true
  | FFIStruct fs1, FFIStruct fs2 -> ffi_field_list_eq fs1 fs2
  | FFIOpaquePtr, FFIOpaquePtr -> true
  | _, _ -> false

and ffi_type_list_eq (ts1 ts2: list ffi_safe_type) : Tot bool (decreases ts1) =
  match ts1, ts2 with
  | [], [] -> true
  | t1 :: r1, t2 :: r2 -> ffi_type_eq t1 t2 && ffi_type_list_eq r1 r2
  | _, _ -> false

and ffi_field_list_eq (fs1 fs2: list (string & ffi_safe_type))
    : Tot bool (decreases fs1) =
  match fs1, fs2 with
  | [], [] -> true
  | (n1, t1) :: r1, (n2, t2) :: r2 ->
      n1 = n2 && ffi_type_eq t1 t2 && ffi_field_list_eq r1 r2
  | _, _ -> false

(** ============================================================================
    MEMORY LAYOUT - PRIMITIVE SIZES AND ALIGNMENTS
    ============================================================================ *)

(* Platform configuration for memory layout calculations.
   This allows platform-aware size/alignment computations without
   requiring the full target_abi type (defined later in the file).

   IMPORTANT: Default values assume LP64 (64-bit Unix-like systems).
   For accurate cross-platform analysis, use the ABI-aware functions
   with an explicit target_abi parameter (defined in the ABI section). *)
noeq type platform_config = {
  pc_pointer_size : nat;   (* Pointer width: 4 for 32-bit, 8 for 64-bit *)
  pc_pointer_align: nat;   (* Pointer alignment (usually equals size) *)
  pc_long_size    : nat;   (* C 'long' size: 4 on LLP64/ILP32, 8 on LP64 *)
  pc_size_t_size  : nat;   (* size_t size: usually equals pointer size *)
}

(* Default platform: LP64 64-bit (Linux, macOS, FreeBSD on x86_64/ARM64) *)
let default_platform_config : platform_config = {
  pc_pointer_size = 8;
  pc_pointer_align = 8;
  pc_long_size = 8;
  pc_size_t_size = 8
}

(* 32-bit platform configuration (ILP32: x86, ARM32, WASM32) *)
let platform_config_32bit : platform_config = {
  pc_pointer_size = 4;
  pc_pointer_align = 4;
  pc_long_size = 4;
  pc_size_t_size = 4
}

(* Windows 64-bit platform configuration (LLP64) *)
let platform_config_windows64 : platform_config = {
  pc_pointer_size = 8;
  pc_pointer_align = 8;
  pc_long_size = 4;   (* Windows: long is 4 bytes even on 64-bit! *)
  pc_size_t_size = 8
}

(* Legacy compatibility: default pointer size/align for quick calculations.
   WARNING: These assume 64-bit platform. For cross-platform code analysis,
   use platform_config or target_abi-aware functions instead. *)
let ptr_size : nat = default_platform_config.pc_pointer_size
let ptr_align : nat = default_platform_config.pc_pointer_align

(* Platform-aware pointer size *)
let ptr_size_for_platform (cfg: platform_config) : nat = cfg.pc_pointer_size
let ptr_align_for_platform (cfg: platform_config) : nat = cfg.pc_pointer_align

(* Integer width to size in bytes - platform-independent for fixed-width types *)
let int_width_size (w: int_width) : nat =
  match w with
  | I8   -> 1
  | I16  -> 2
  | I32  -> 4
  | I64  -> 8
  | I128 -> 16
  | IBig -> 8  (* BigInt is represented as a pointer - uses default platform *)

(* Platform-aware integer width size (only IBig varies by platform) *)
let int_width_size_for_platform (cfg: platform_config) (w: int_width) : nat =
  match w with
  | I8   -> 1
  | I16  -> 2
  | I32  -> 4
  | I64  -> 8
  | I128 -> 16
  | IBig -> cfg.pc_pointer_size  (* BigInt heap pointer is platform-specific *)

(* Float precision to size in bytes - always platform-independent (IEEE 754) *)
let float_prec_size (p: float_prec) : nat =
  match p with
  | F16 -> 2
  | F32 -> 4
  | F64 -> 8

(** ============================================================================
    POWER OF TWO PROOFS
    ============================================================================ *)

(* Check if n is a power of 2 (or 0, which we treat as 1 for alignment) *)
let rec is_power_of_two (n: nat) : Tot bool (decreases n) =
  if n = 0 then true       (* 0 treated as default alignment 1 *)
  else if n = 1 then true
  else if n % 2 <> 0 then false
  else is_power_of_two (n / 2)

(* Lemma: specific values are powers of 2 *)
val is_power_of_two_1 : unit -> Lemma (is_power_of_two 1 = true)
let is_power_of_two_1 () = assert_norm (is_power_of_two 1 = true)

val is_power_of_two_2 : unit -> Lemma (is_power_of_two 2 = true)
let is_power_of_two_2 () = assert_norm (is_power_of_two 2 = true)

val is_power_of_two_4 : unit -> Lemma (is_power_of_two 4 = true)
let is_power_of_two_4 () = assert_norm (is_power_of_two 4 = true)

val is_power_of_two_8 : unit -> Lemma (is_power_of_two 8 = true)
let is_power_of_two_8 () = assert_norm (is_power_of_two 8 = true)

val is_power_of_two_16 : unit -> Lemma (is_power_of_two 16 = true)
let is_power_of_two_16 () = assert_norm (is_power_of_two 16 = true)

(* Alignment for integer types is always a power of 2 *)
val int_width_align_is_pow2 : w:int_width ->
  Lemma (is_power_of_two (int_width_size w) = true)
let int_width_align_is_pow2 w =
  match w with
  | I8   -> is_power_of_two_1 ()
  | I16  -> is_power_of_two_2 ()
  | I32  -> is_power_of_two_4 ()
  | I64  -> is_power_of_two_8 ()
  | I128 -> is_power_of_two_16 ()
  | IBig -> is_power_of_two_8 ()

(* Alignment for float types is always a power of 2 *)
val float_prec_align_is_pow2 : p:float_prec ->
  Lemma (is_power_of_two (float_prec_size p) = true)
let float_prec_align_is_pow2 p =
  match p with
  | F16 -> is_power_of_two_2 ()
  | F32 -> is_power_of_two_4 ()
  | F64 -> is_power_of_two_8 ()

(* Pointer alignment is power of 2 - for default 64-bit platform *)
val ptr_align_is_pow2 : unit -> Lemma (is_power_of_two ptr_align = true)
let ptr_align_is_pow2 () = is_power_of_two_8 ()

(* Platform-aware pointer alignment lemma *)
val ptr_align_for_platform_is_pow2 : cfg:platform_config ->
  Lemma (requires cfg.pc_pointer_align = 4 \/ cfg.pc_pointer_align = 8)
        (ensures is_power_of_two (ptr_align_for_platform cfg) = true)
let ptr_align_for_platform_is_pow2 cfg =
  if cfg.pc_pointer_align = 4 then is_power_of_two_4 ()
  else is_power_of_two_8 ()

(* Platform-aware integer alignment lemma for IBig *)
val int_width_align_for_platform_is_pow2 : cfg:platform_config -> w:int_width ->
  Lemma (requires cfg.pc_pointer_size = 4 \/ cfg.pc_pointer_size = 8)
        (ensures is_power_of_two (int_width_size_for_platform cfg w) = true)
let int_width_align_for_platform_is_pow2 cfg w =
  match w with
  | I8   -> is_power_of_two_1 ()
  | I16  -> is_power_of_two_2 ()
  | I32  -> is_power_of_two_4 ()
  | I64  -> is_power_of_two_8 ()
  | I128 -> is_power_of_two_16 ()
  | IBig ->
      if cfg.pc_pointer_size = 4 then is_power_of_two_4 ()
      else is_power_of_two_8 ()

(** ============================================================================
    FFI TYPE SIZE AND ALIGNMENT
    ============================================================================ *)

(* Round up to alignment boundary - not recursive, defined first *)
let align_up (offset: nat) (align: nat) : nat =
  if align = 0 then offset
  else
    let remainder = offset % align in
    if remainder = 0 then offset
    else offset + (align - remainder)

(* Simple size/alignment for non-struct types - no recursion needed *)
let ffi_primitive_size (t: ffi_safe_type) : option nat =
  match t with
  | FFIInt w _ -> Some (int_width_size w)
  | FFIFloat p -> Some (float_prec_size p)
  | FFIPtr _ -> Some ptr_size
  | FFIFnPtr _ _ -> Some ptr_size
  | FFICStr -> Some ptr_size
  | FFIVoid -> Some 0
  | FFIOpaquePtr -> Some ptr_size
  | FFIStruct _ -> None  (* Struct needs recursive computation *)

let ffi_primitive_align (t: ffi_safe_type) : option nat =
  match t with
  | FFIInt w _ -> Some (int_width_size w)
  | FFIFloat p -> Some (float_prec_size p)
  | FFIPtr _ -> Some ptr_align
  | FFIFnPtr _ _ -> Some ptr_align
  | FFICStr -> Some ptr_align
  | FFIVoid -> Some 1
  | FFIOpaquePtr -> Some ptr_align
  | FFIStruct _ -> None  (* Struct needs recursive computation *)

(* Size of FFI type in bytes - using structural recursion on type *)
let rec ffi_type_size (t: ffi_safe_type) : Tot nat (decreases t) =
  match t with
  | FFIInt w _ -> int_width_size w
  | FFIFloat p -> float_prec_size p
  | FFIPtr _ -> ptr_size
  | FFIFnPtr _ _ -> ptr_size
  | FFICStr -> ptr_size
  | FFIVoid -> 0
  | FFIOpaquePtr -> ptr_size
  | FFIStruct fields -> compute_struct_size_aux fields 0 1

(* Alignment of FFI type in bytes *)
and ffi_type_align (t: ffi_safe_type) : Tot nat (decreases t) =
  match t with
  | FFIInt w _ -> int_width_size w
  | FFIFloat p -> float_prec_size p
  | FFIPtr _ -> ptr_align
  | FFIFnPtr _ _ -> ptr_align
  | FFICStr -> ptr_align
  | FFIVoid -> 1
  | FFIOpaquePtr -> ptr_align
  | FFIStruct fields -> compute_struct_align_aux fields

(* Maximum alignment of struct fields *)
and compute_struct_align_aux (fields: list (string & ffi_safe_type)) : Tot nat (decreases fields) =
  match fields with
  | [] -> 1
  | (_, t) :: rest ->
      let field_align = ffi_type_align t in
      let rest_align = compute_struct_align_aux rest in
      if field_align >= rest_align then field_align else rest_align

(* Compute struct size with padding (C layout algorithm)
   Accumulator-based: current_offset and max_align *)
and compute_struct_size_aux
    (fields: list (string & ffi_safe_type))
    (current_offset: nat)
    (max_align: nat)
    : Tot nat (decreases fields) =
  match fields with
  | [] -> align_up current_offset max_align
  | (_, t) :: rest ->
      let field_size = ffi_type_size t in
      let field_align = ffi_type_align t in
      let new_max_align = if field_align > max_align then field_align else max_align in
      let aligned_offset = align_up current_offset field_align in
      let next_offset = aligned_offset + field_size in
      compute_struct_size_aux rest next_offset new_max_align

(* Wrapper for external use *)
let compute_struct_size (fields: list (string & ffi_safe_type)) : nat =
  compute_struct_size_aux fields 0 1

let compute_struct_align (fields: list (string & ffi_safe_type)) : nat =
  compute_struct_align_aux fields

(** ============================================================================
    STRUCT LAYOUT COMPUTATION - DETAILED
    ============================================================================ *)

(* Field layout information: name, offset, size *)
type field_layout = {
  fl_name   : string;
  fl_offset : nat;
  fl_size   : nat
}

(* Helper: compute layout with offset accumulator *)
let rec compute_c_layout_aux
    (fields: list (string & ffi_safe_type))
    (current_offset: nat)
    : Tot (list field_layout) (decreases fields) =
  match fields with
  | [] -> []
  | (name, t) :: rest ->
      let field_size = ffi_type_size t in
      let field_align = ffi_type_align t in
      let aligned_offset = align_up current_offset field_align in
      let layout = { fl_name = name; fl_offset = aligned_offset; fl_size = field_size } in
      layout :: compute_c_layout_aux rest (aligned_offset + field_size)

(* Compute C-style struct layout with field offsets *)
let compute_c_layout (fields: list (string & ffi_safe_type)) : list field_layout =
  compute_c_layout_aux fields 0

(* Alternative return format: list (name, offset, size) *)
let compute_c_layout_tuples (fields: list (string & ffi_safe_type))
    : list (string & nat & nat) =
  let layouts = compute_c_layout fields in
  map (fun fl -> (fl.fl_name, fl.fl_offset, fl.fl_size)) layouts

(** ============================================================================
    ALIGNMENT PROOF - ALL ALIGNMENTS ARE POWERS OF 2
    ============================================================================ *)

(* Lemma: max of two powers of 2 is a power of 2 *)
val max_pow2_is_pow2 : a:nat -> b:nat ->
  Lemma (requires is_power_of_two a = true /\ is_power_of_two b = true)
        (ensures is_power_of_two (if a >= b then a else b) = true)
let max_pow2_is_pow2 a b =
  if a >= b then () else ()

(* Lemma: FFI type alignment is always a power of 2 *)
val ffi_type_align_is_pow2 : t:ffi_safe_type ->
  Lemma (ensures is_power_of_two (ffi_type_align t) = true)
        (decreases t)
let rec ffi_type_align_is_pow2 t =
  match t with
  | FFIInt w _ -> int_width_align_is_pow2 w
  | FFIFloat p -> float_prec_align_is_pow2 p
  | FFIPtr _ -> ptr_align_is_pow2 ()
  | FFIFnPtr _ _ -> ptr_align_is_pow2 ()
  | FFICStr -> ptr_align_is_pow2 ()
  | FFIVoid -> is_power_of_two_1 ()
  | FFIStruct fields -> struct_align_is_pow2 fields
  | FFIOpaquePtr -> ptr_align_is_pow2 ()

(* Lemma: struct alignment (max of field alignments) is power of 2 *)
and struct_align_is_pow2 (fields: list (string & ffi_safe_type)) :
  Lemma (ensures is_power_of_two (compute_struct_align fields) = true)
        (decreases fields) =
  match fields with
  | [] -> is_power_of_two_1 ()
  | (_, t) :: rest ->
      ffi_type_align_is_pow2 t;
      struct_align_is_pow2 rest;
      max_pow2_is_pow2 (ffi_type_align t) (compute_struct_align rest)

(** ============================================================================
    LAYOUT CORRECTNESS PROOFS
    ============================================================================ *)

(* Lemma: align_up produces offset >= original *)
val align_up_ge : offset:nat -> align:nat ->
  Lemma (align_up offset align >= offset)
let align_up_ge offset align =
  if align = 0 then ()
  else
    let remainder = offset % align in
    if remainder = 0 then ()
    else ()

(* Lemma: align_up produces aligned result *)
val align_up_aligned : offset:nat -> align:nat{align > 0} ->
  Lemma (align_up offset align % align = 0)
let align_up_aligned offset align =
  let remainder = offset % align in
  if remainder = 0 then ()
  else
    (* offset + (align - remainder) *)
    (* (offset + align - remainder) % align = (offset % align + align - remainder) % align *)
    (* = (remainder + align - remainder) % align = align % align = 0 *)
    ()

(* Helper: get first field offset, or 0 if empty *)
let first_field_offset (layouts: list field_layout) : nat =
  match layouts with
  | [] -> 0
  | fl :: _ -> fl.fl_offset

(* Lemma: field offsets in layout are non-decreasing *)
val layout_offsets_increasing : fields:list (string & ffi_safe_type) -> offset:nat ->
  Lemma (ensures first_field_offset (compute_c_layout_aux fields offset) >= offset \/
                 Nil? (compute_c_layout_aux fields offset))
  (decreases fields)
let layout_offsets_increasing fields offset =
  match fields with
  | [] -> ()
  | (name, t) :: rest ->
      let field_align = ffi_type_align t in
      align_up_ge offset field_align

(** ============================================================================
    FFI SAFETY CHECKING - CONVERTING BRRR_TYPE TO FFI_SAFE_TYPE
    ============================================================================ *)

(* Detailed error type for FFI safety checking.
   Provides specific information about why a type is not FFI-safe. *)
type ffi_safety_error =
  | FFISafeErrNeverType
      (* Never type has no representation *)
  | FFISafeErrDynamicType
      (* Dynamic type has no fixed representation *)
  | FFISafeErrBigInt
      (* BigInt is heap-allocated with GC, not C-compatible *)
  | FFISafeErrNonCRepr : repr:repr_attr -> ffi_safety_error
      (* Struct has non-C representation *)
  | FFISafeErrNonUnsafeFunction
      (* Only unsafe functions can cross FFI boundary *)
  | FFISafeErrUnsupportedWrapper : wrapper:wrapper_kind -> ffi_safety_error
      (* Wrapper type is not FFI-compatible (Rc, Arc, Option, etc.) *)
  | FFISafeErrNestedField : struct_name:string -> field_name:string ->
                            inner_error:ffi_safety_error -> ffi_safety_error
      (* Field type in struct is not FFI-safe *)
  | FFISafeErrNestedParam : param_idx:nat -> inner_error:ffi_safety_error -> ffi_safety_error
      (* Function parameter type is not FFI-safe *)
  | FFISafeErrNestedReturn : inner_error:ffi_safety_error -> ffi_safety_error
      (* Function return type is not FFI-safe *)
  | FFISafeErrUnsupportedType : type_desc:string -> ffi_safety_error
      (* Catch-all for types without FFI representation *)

(* Convert FFI safety error to human-readable string *)
let rec ffi_safety_error_to_string (err: ffi_safety_error) : Tot string (decreases err) =
  match err with
  | FFISafeErrNeverType ->
      "Never type (!) has no representation and cannot cross FFI boundary"
  | FFISafeErrDynamicType ->
      "Dynamic type (dyn) has no fixed representation for FFI"
  | FFISafeErrBigInt ->
      "BigInt is garbage-collected and cannot be safely passed to C; use fixed-width integer instead"
  | FFISafeErrNonCRepr ReprRust ->
      "Struct has Rust repr (default) which has no guaranteed layout; add #[repr(C)] attribute"
  | FFISafeErrNonCRepr r ->
      "Struct representation is not C-compatible"
  | FFISafeErrNonUnsafeFunction ->
      "Only unsafe functions can be passed across FFI boundary as function pointers"
  | FFISafeErrUnsupportedWrapper WRc ->
      "Rc<T> is not FFI-safe (reference-counted pointer with runtime); use raw pointer instead"
  | FFISafeErrUnsupportedWrapper WArc ->
      "Arc<T> is not FFI-safe (atomic reference count); use raw pointer instead"
  | FFISafeErrUnsupportedWrapper WOption ->
      "Option<T> is not FFI-safe (has Rust-specific layout); use nullable pointer for Option<Box<T>>"
  | FFISafeErrUnsupportedWrapper WMut ->
      "Mut<T> (mutable reference wrapper) is not FFI-safe; use raw mutable pointer"
  | FFISafeErrUnsupportedWrapper w ->
      "Wrapper type is not FFI-compatible"
  | FFISafeErrNestedField sname fname inner ->
      "In struct '" ^ sname ^ "', field '" ^ fname ^ "' is not FFI-safe: " ^
      ffi_safety_error_to_string inner
  | FFISafeErrNestedParam idx inner ->
      "Function parameter " ^ string_of_int idx ^ " is not FFI-safe: " ^
      ffi_safety_error_to_string inner
  | FFISafeErrNestedReturn inner ->
      "Function return type is not FFI-safe: " ^ ffi_safety_error_to_string inner
  | FFISafeErrUnsupportedType desc ->
      "Type '" ^ desc ^ "' has no FFI representation"

(* FFI safety check result with detailed errors *)
type ffi_safety_result =
  | FFISafeOk : ffi_type:ffi_safe_type -> ffi_safety_result
  | FFISafeErr : error:ffi_safety_error -> ffi_safety_result

(* Detailed FFI safety check with error information.
   Returns either the FFI-safe type conversion or a detailed error explaining
   why the type cannot cross the FFI boundary. *)
let rec check_ffi_safe (t: brrr_type) : ffi_safety_result =
  match t with
  (* Unit maps to void *)
  | TPrim PUnit -> FFISafeOk FFIVoid

  (* Never is not FFI-safe (no representation) *)
  | TPrim PNever -> FFISafeErr FFISafeErrNeverType

  (* Bool maps to i8 (C99 _Bool, typically 1 byte) *)
  | TPrim PBool -> FFISafeOk (FFIInt I8 Unsigned)

  (* String is a C string pointer *)
  | TPrim PString -> FFISafeOk FFICStr

  (* Char maps to u32 (Unicode codepoint, but FFI uses u8 for C char) *)
  | TPrim PChar -> FFISafeOk (FFIInt I8 Unsigned)

  (* Dynamic type is not FFI-safe *)
  | TPrim PDynamic -> FFISafeErr FFISafeErrDynamicType

  (* Integers are FFI-safe if not IBig *)
  | TNumeric (NumInt it) ->
      if it.width = IBig then FFISafeErr FFISafeErrBigInt
      else FFISafeOk (FFIInt it.width it.sign)

  (* Floats are FFI-safe (except F16 which has limited support) *)
  | TNumeric (NumFloat p) -> FFISafeOk (FFIFloat p)

  (* Raw pointers are FFI-safe if inner type is *)
  | TWrap WRaw inner ->
      (match check_ffi_safe inner with
       | FFISafeOk inner_ffi -> FFISafeOk (FFIPtr inner_ffi)
       | FFISafeErr _ -> FFISafeOk FFIOpaquePtr)  (* Fall back to opaque pointer *)

  (* Box pointers become raw pointers in FFI *)
  | TWrap WBox inner ->
      (match check_ffi_safe inner with
       | FFISafeOk inner_ffi -> FFISafeOk (FFIPtr inner_ffi)
       | FFISafeErr _ -> FFISafeOk FFIOpaquePtr)

  (* Other wrappers are not FFI-safe *)
  | TWrap w _ -> FFISafeErr (FFISafeErrUnsupportedWrapper w)

  (* Structs with ReprC are FFI-safe *)
  | TStruct st ->
      (match st.struct_repr with
       | ReprC ->
           (match check_fields_ffi_safe st.struct_name st.struct_fields with
            | FFISafeOk ffi_fields -> FFISafeOk (FFIStruct ffi_fields)
            | FFISafeErr err -> FFISafeErr err)
       | r -> FFISafeErr (FFISafeErrNonCRepr r))

  (* Function types map to function pointers *)
  | TFunc ft ->
      if ft.is_unsafe then
        (match check_params_ffi_safe ft.params 0 with
         | FFISafeErr err -> FFISafeErr err
         | FFISafeOk ffi_params ->
             match check_ffi_safe ft.return_type with
             | FFISafeErr err -> FFISafeErr (FFISafeErrNestedReturn err)
             | FFISafeOk ffi_ret -> FFISafeOk (FFIFnPtr ffi_params ffi_ret))
      else FFISafeErr FFISafeErrNonUnsafeFunction

  (* All other types are not FFI-safe *)
  | _ -> FFISafeErr (FFISafeErrUnsupportedType "unknown")

(* Check struct fields for FFI safety with detailed errors *)
and check_fields_ffi_safe (struct_name: string) (fields: list field_type)
    : ffi_safety_result =
  match fields with
  | [] -> FFISafeOk []
  | f :: rest ->
      match check_ffi_safe f.field_ty with
      | FFISafeErr err -> FFISafeErr (FFISafeErrNestedField struct_name f.field_name err)
      | FFISafeOk ffi_ty ->
          match check_fields_ffi_safe struct_name rest with
          | FFISafeErr err -> FFISafeErr err
          | FFISafeOk ffi_rest -> FFISafeOk ((f.field_name, ffi_ty) :: ffi_rest)

(* Check function parameters for FFI safety with detailed errors *)
and check_params_ffi_safe (params: list param_type) (idx: nat)
    : ffi_safety_result =
  match params with
  | [] -> FFISafeOk []
  | p :: rest ->
      match check_ffi_safe p.ty with
      | FFISafeErr err -> FFISafeErr (FFISafeErrNestedParam idx err)
      | FFISafeOk ffi_ty ->
          match check_params_ffi_safe rest (idx + 1) with
          | FFISafeErr err -> FFISafeErr err
          | FFISafeOk ffi_rest -> FFISafeOk (ffi_ty :: ffi_rest)

(* Legacy API: Check if a brrr_type can be used in FFI and convert it.
   Returns None if the type is not FFI-safe.
   For detailed error information, use check_ffi_safe instead. *)
let rec is_ffi_safe (t: brrr_type) : option ffi_safe_type =
  match check_ffi_safe t with
  | FFISafeOk ffi_ty -> Some ffi_ty
  | FFISafeErr _ -> None

(* Convert struct fields to FFI fields - legacy API *)
and convert_fields_to_ffi (fields: list field_type)
    : option (list (string & ffi_safe_type)) =
  match fields with
  | [] -> Some []
  | f :: rest ->
      (match is_ffi_safe f.field_ty, convert_fields_to_ffi rest with
       | Some ffi_ty, Some ffi_rest -> Some ((f.field_name, ffi_ty) :: ffi_rest)
       | _, _ -> None)

(* Convert function parameters to FFI types - legacy API *)
and convert_params_to_ffi (params: list param_type)
    : option (list ffi_safe_type) =
  match params with
  | [] -> Some []
  | p :: rest ->
      (match is_ffi_safe p.ty, convert_params_to_ffi rest with
       | Some ffi_ty, Some ffi_rest -> Some (ffi_ty :: ffi_rest)
       | _, _ -> None)

(* Get detailed error when is_ffi_safe returns None *)
let get_ffi_safety_error (t: brrr_type) : option ffi_safety_error =
  match check_ffi_safe t with
  | FFISafeOk _ -> None
  | FFISafeErr err -> Some err

(* Check FFI safety and get either result or formatted error message *)
let check_ffi_safe_with_message (t: brrr_type) : either ffi_safe_type string =
  match check_ffi_safe t with
  | FFISafeOk ffi_ty -> Inl ffi_ty
  | FFISafeErr err -> Inr (ffi_safety_error_to_string err)

(** ============================================================================
    FOREIGN FUNCTION DECLARATION
    ============================================================================ *)

(* Extern function declaration with visibility control *)
noeq type extern_fn = {
  fn_name       : string;                         (* Symbol name *)
  fn_convention : calling_convention;             (* Calling convention *)
  fn_params     : list (string & ffi_safe_type);  (* Named parameters *)
  fn_return     : ffi_safe_type;                  (* Return type *)
  fn_is_variadic: bool;                           (* Is variadic (printf-style)? *)
  fn_link_name  : option string;                  (* Optional different link name *)
  fn_visibility : ffi_visibility                  (* FFI boundary visibility *)
}

(* Create simple extern function declaration (default: public) *)
let make_extern_fn
    (name: string)
    (params: list (string & ffi_safe_type))
    (ret: ffi_safe_type)
    : extern_fn =
  {
    fn_name = name;
    fn_convention = CC_C;
    fn_params = params;
    fn_return = ret;
    fn_is_variadic = false;
    fn_link_name = None;
    fn_visibility = FFIPublic
  }

(* Create extern function with specific visibility *)
let make_extern_fn_with_visibility
    (name: string)
    (params: list (string & ffi_safe_type))
    (ret: ffi_safe_type)
    (vis: ffi_visibility)
    : extern_fn =
  { make_extern_fn name params ret with fn_visibility = vis }

(* Create private extern function (internal use only) *)
let make_private_extern_fn
    (name: string)
    (params: list (string & ffi_safe_type))
    (ret: ffi_safe_type)
    : extern_fn =
  { make_extern_fn name params ret with fn_visibility = FFIPrivate }

(* Create internal extern function (crate-visible only) *)
let make_internal_extern_fn
    (name: string)
    (params: list (string & ffi_safe_type))
    (ret: ffi_safe_type)
    : extern_fn =
  { make_extern_fn name params ret with fn_visibility = FFIInternal }

(* Create variadic extern function *)
let make_variadic_extern_fn
    (name: string)
    (params: list (string & ffi_safe_type))
    (ret: ffi_safe_type)
    : extern_fn =
  { make_extern_fn name params ret with fn_is_variadic = true }

(* Get the actual link name for the function *)
let extern_link_name (fn: extern_fn) : string =
  match fn.fn_link_name with
  | Some name -> name
  | None -> fn.fn_name

(* Check if extern function should be exported across FFI boundary *)
let should_export_extern (fn: extern_fn) : bool =
  is_ffi_exported fn.fn_visibility

(* Check if extern function is accessible within current crate *)
let is_extern_internally_accessible (fn: extern_fn) : bool =
  is_internally_visible fn.fn_visibility

(** ============================================================================
    VISIBILITY VERIFICATION FOR FFI EXPORTS
    ============================================================================ *)

(* FFI export validation error *)
type ffi_visibility_error =
  | VisErrPrivateExport : fn_name:string -> ffi_visibility_error
      (* Attempting to export a private function *)
  | VisErrInternalExport : fn_name:string -> ffi_visibility_error
      (* Attempting to export an internal function *)
  | VisErrParamTypeNotPublic : fn_name:string -> param_name:string -> ffi_visibility_error
      (* Parameter type references non-public type *)

(* Check that function visibility is valid for FFI export *)
let check_extern_visibility (fn: extern_fn) (exporting: bool) : option ffi_visibility_error =
  if exporting && fn.fn_visibility = FFIPrivate then
    Some (VisErrPrivateExport fn.fn_name)
  else if exporting && fn.fn_visibility = FFIInternal then
    Some (VisErrInternalExport fn.fn_name)
  else
    None

(* Validate a list of extern functions for export *)
let rec validate_extern_visibility (fns: list extern_fn) (exporting: bool)
    : list ffi_visibility_error =
  match fns with
  | [] -> []
  | fn :: rest ->
      match check_extern_visibility fn exporting with
      | Some err -> err :: validate_extern_visibility rest exporting
      | None -> validate_extern_visibility rest exporting

(** ============================================================================
    UNSAFE EFFECTS AND CHECKING
    ============================================================================ *)

(* Unsafe operation kinds *)
type unsafe_effect =
  | UnsafeFFI       : unsafe_effect   (* Foreign function call *)
  | UnsafePtr       : unsafe_effect   (* Raw pointer operations *)
  | UnsafeTransmute : unsafe_effect   (* Type transmutation *)
  | UnsafeAsm       : unsafe_effect   (* Inline assembly *)
  | UnsafeUnion     : unsafe_effect   (* Union field access *)

(* Unsafe context: tracks what unsafe operations are allowed *)
noeq type unsafe_context = {
  uc_in_unsafe_block : bool;           (* Inside explicit unsafe block? *)
  uc_in_unsafe_fn    : bool;           (* Inside unsafe function? *)
  uc_allowed_ops     : list unsafe_effect  (* Specific allowed operations *)
}

(* Empty unsafe context (nothing allowed) *)
let no_unsafe : unsafe_context = {
  uc_in_unsafe_block = false;
  uc_in_unsafe_fn = false;
  uc_allowed_ops = []
}

(* Context inside unsafe block *)
let in_unsafe_block : unsafe_context = {
  uc_in_unsafe_block = true;
  uc_in_unsafe_fn = false;
  uc_allowed_ops = [UnsafeFFI; UnsafePtr; UnsafeTransmute; UnsafeAsm; UnsafeUnion]
}

(* Context inside unsafe function *)
let in_unsafe_fn : unsafe_context = {
  uc_in_unsafe_block = false;
  uc_in_unsafe_fn = true;
  uc_allowed_ops = [UnsafeFFI; UnsafePtr; UnsafeTransmute; UnsafeAsm; UnsafeUnion]
}

(* Check if unsafe operation is allowed *)
let is_unsafe_allowed (op: unsafe_effect) (ctx: unsafe_context) : bool =
  ctx.uc_in_unsafe_block || ctx.uc_in_unsafe_fn ||
  List.Tot.mem op ctx.uc_allowed_ops

(* Check if FFI call is allowed (must be in unsafe context) *)
let check_ffi_call (fn: extern_fn) (ctx: unsafe_context) : bool =
  is_unsafe_allowed UnsafeFFI ctx

(* Simplified check: FFI call requires unsafe *)
let check_ffi_call_simple (fn: extern_fn) : bool =
  (* This function just documents that FFI calls need unsafe context.
     Actual checking is done by check_ffi_call with context. *)
  false  (* Default: FFI calls are not allowed without unsafe *)

(** ============================================================================
    FORMAT STRING ANALYSIS FOR PRINTF-FAMILY FUNCTIONS
    ============================================================================

    Validates format strings against variadic arguments to detect:
    - Format/argument count mismatches
    - Format/argument type mismatches
    - Buffer overflow risks from %s without length limits
    - Format string injection vulnerabilities

    Supported format specifiers (C99/POSIX):
    %d, %i     - signed int
    %u         - unsigned int
    %x, %X     - unsigned int (hex)
    %o         - unsigned int (octal)
    %f, %F     - double
    %e, %E     - double (scientific)
    %g, %G     - double (auto)
    %c         - char (int)
    %s         - char pointer (null-terminated string)
    %p         - void pointer
    %n         - int pointer (DANGEROUS - disabled by default)
    %%         - literal percent

    Length modifiers:
    hh, h      - char/short
    l          - long
    ll         - long long
    L          - long double
    z          - size_t
    j          - intmax_t
    t          - ptrdiff_t
    ============================================================================ *)

(* Format specifier types *)
type format_specifier =
  | FmtSignedInt      : format_specifier   (* %d, %i *)
  | FmtUnsignedInt    : format_specifier   (* %u *)
  | FmtHex            : format_specifier   (* %x, %X *)
  | FmtOctal          : format_specifier   (* %o *)
  | FmtFloat          : format_specifier   (* %f, %F, %e, %E, %g, %G *)
  | FmtChar           : format_specifier   (* %c *)
  | FmtString         : format_specifier   (* %s *)
  | FmtPointer        : format_specifier   (* %p *)
  | FmtWriteCount     : format_specifier   (* %n - dangerous! *)
  | FmtPercent        : format_specifier   (* %% *)

(* Length modifiers affect expected argument type *)
type length_modifier =
  | LenNone   : length_modifier   (* default *)
  | LenHH     : length_modifier   (* hh - char *)
  | LenH      : length_modifier   (* h - short *)
  | LenL      : length_modifier   (* l - long *)
  | LenLL     : length_modifier   (* ll - long long *)
  | LenBigL   : length_modifier   (* L - long double *)
  | LenZ      : length_modifier   (* z - size_t *)
  | LenJ      : length_modifier   (* j - intmax_t *)
  | LenT      : length_modifier   (* t - ptrdiff_t *)

(* Parsed format directive *)
noeq type format_directive = {
  fd_specifier    : format_specifier;
  fd_length       : length_modifier;
  fd_width        : option nat;       (* field width, if specified *)
  fd_precision    : option nat;       (* precision, if specified *)
  fd_position     : nat;              (* position in format string *)
}

(* Format string analysis error *)
type format_error =
  | FmtErrInvalidSpecifier : position:nat -> char_code:nat -> format_error
      (* Unrecognized format specifier *)
  | FmtErrTooFewArgs : expected:nat -> actual:nat -> format_error
      (* Fewer arguments than format specifiers *)
  | FmtErrTooManyArgs : expected:nat -> actual:nat -> format_error
      (* More arguments than format specifiers *)
  | FmtErrTypeMismatch : position:nat -> expected:format_specifier ->
                         actual:ffi_safe_type -> format_error
      (* Argument type does not match format specifier *)
  | FmtErrDangerousN : position:nat -> format_error
      (* %n specifier is security risk *)
  | FmtErrUnboundedString : position:nat -> format_error
      (* %s without precision limit is potential buffer overflow *)
  | FmtErrNullFormatString : format_error
      (* Format string itself may be null *)

(* Convert format specifier to string for diagnostics *)
let format_specifier_to_string (spec: format_specifier) : string =
  match spec with
  | FmtSignedInt -> "%d/%i"
  | FmtUnsignedInt -> "%u"
  | FmtHex -> "%x/%X"
  | FmtOctal -> "%o"
  | FmtFloat -> "%f/%e/%g"
  | FmtChar -> "%c"
  | FmtString -> "%s"
  | FmtPointer -> "%p"
  | FmtWriteCount -> "%n"
  | FmtPercent -> "%%"

(* Convert format error to string *)
let format_error_to_string (err: format_error) : string =
  match err with
  | FmtErrInvalidSpecifier pos _ ->
      "Invalid format specifier at position " ^ string_of_int pos
  | FmtErrTooFewArgs exp act ->
      "Too few arguments: expected " ^ string_of_int exp ^
      ", got " ^ string_of_int act
  | FmtErrTooManyArgs exp act ->
      "Too many arguments: expected " ^ string_of_int exp ^
      ", got " ^ string_of_int act
  | FmtErrTypeMismatch pos exp _ ->
      "Type mismatch at position " ^ string_of_int pos ^
      ": expected type for " ^ format_specifier_to_string exp
  | FmtErrDangerousN pos ->
      "Dangerous %n specifier at position " ^ string_of_int pos ^
      " (allows arbitrary memory write)"
  | FmtErrUnboundedString pos ->
      "Unbounded %s at position " ^ string_of_int pos ^
      " (potential buffer overflow, use %.Ns to limit)"
  | FmtErrNullFormatString ->
      "Format string may be null"

(* Get expected FFI type for format specifier with length modifier *)
let expected_type_for_format
    (spec: format_specifier)
    (len: length_modifier)
    (cfg: platform_config)
    : option ffi_safe_type =
  match spec with
  | FmtPercent -> None  (* %% consumes no argument *)
  | FmtSignedInt ->
      (match len with
       | LenHH -> Some (FFIInt I8 Signed)
       | LenH -> Some (FFIInt I16 Signed)
       | LenNone -> Some (FFIInt I32 Signed)
       | LenL ->
           if cfg.pc_long_size = 8 then Some (FFIInt I64 Signed)
           else Some (FFIInt I32 Signed)
       | LenLL -> Some (FFIInt I64 Signed)
       | LenZ -> (* size_t is unsigned, but %zd allows signed *)
           if cfg.pc_size_t_size = 8 then Some (FFIInt I64 Signed)
           else Some (FFIInt I32 Signed)
       | LenJ -> Some (FFIInt I64 Signed)  (* intmax_t *)
       | LenT -> (* ptrdiff_t *)
           if cfg.pc_pointer_size = 8 then Some (FFIInt I64 Signed)
           else Some (FFIInt I32 Signed)
       | _ -> Some (FFIInt I32 Signed))
  | FmtUnsignedInt | FmtHex | FmtOctal ->
      (match len with
       | LenHH -> Some (FFIInt I8 Unsigned)
       | LenH -> Some (FFIInt I16 Unsigned)
       | LenNone -> Some (FFIInt I32 Unsigned)
       | LenL ->
           if cfg.pc_long_size = 8 then Some (FFIInt I64 Unsigned)
           else Some (FFIInt I32 Unsigned)
       | LenLL -> Some (FFIInt I64 Unsigned)
       | LenZ ->
           if cfg.pc_size_t_size = 8 then Some (FFIInt I64 Unsigned)
           else Some (FFIInt I32 Unsigned)
       | LenJ -> Some (FFIInt I64 Unsigned)  (* uintmax_t *)
       | LenT ->
           if cfg.pc_pointer_size = 8 then Some (FFIInt I64 Unsigned)
           else Some (FFIInt I32 Unsigned)
       | _ -> Some (FFIInt I32 Unsigned))
  | FmtFloat ->
      (match len with
       | LenBigL -> Some (FFIFloat F64)  (* long double - approximate as double *)
       | _ -> Some (FFIFloat F64))
  | FmtChar -> Some (FFIInt I32 Signed)  (* char promoted to int in varargs *)
  | FmtString -> Some FFICStr
  | FmtPointer -> Some FFIOpaquePtr
  | FmtWriteCount ->
      (* %n writes to int pointer - extremely dangerous *)
      Some (FFIPtr (FFIInt I32 Signed))

(* Check if actual type is compatible with expected format type *)
let type_matches_format
    (expected: ffi_safe_type)
    (actual: ffi_safe_type)
    : bool =
  (* Exact match *)
  if ffi_type_eq expected actual then true
  (* Integer promotion: smaller signed -> larger signed is OK *)
  else match expected, actual with
  | FFIInt exp_w exp_s, FFIInt act_w act_s ->
      (* Unsigned -> unsigned or signed -> signed, width must match or widen *)
      exp_s = act_s &&
      int_width_size act_w <= int_width_size exp_w
  (* Pointer types: void* accepts any pointer *)
  | FFIOpaquePtr, FFIPtr _ -> true
  | FFIOpaquePtr, FFIOpaquePtr -> true
  | FFIPtr _, FFIOpaquePtr -> true  (* May be unsafe but allowed *)
  (* C string accepts any char pointer *)
  | FFICStr, FFIPtr (FFIInt I8 _) -> true
  | FFIPtr (FFIInt I8 _), FFICStr -> true
  | _, _ -> false

(* Format string analysis result *)
noeq type format_analysis_result = {
  far_directives  : list format_directive;  (* Parsed format directives *)
  far_arg_count   : nat;                    (* Expected argument count *)
  far_errors      : list format_error;      (* Analysis errors *)
  far_warnings    : list format_error;      (* Analysis warnings *)
}

(* Validate format arguments against parsed directives *)
let rec validate_format_args_aux
    (directives: list format_directive)
    (args: list ffi_safe_type)
    (cfg: platform_config)
    (arg_idx: nat)
    : list format_error =
  match directives with
  | [] ->
      (* Check for extra arguments *)
      if Cons? args then [FmtErrTooManyArgs arg_idx (arg_idx + List.Tot.length args)]
      else []
  | dir :: rest ->
      match dir.fd_specifier with
      | FmtPercent ->
          (* %% consumes no argument *)
          validate_format_args_aux rest args cfg arg_idx
      | _ ->
          match expected_type_for_format dir.fd_specifier dir.fd_length cfg with
          | None -> validate_format_args_aux rest args cfg arg_idx
          | Some expected_ty ->
              match args with
              | [] -> [FmtErrTooFewArgs (arg_idx + 1 + List.Tot.length rest) arg_idx]
              | actual :: rest_args ->
                  let type_errors =
                    if type_matches_format expected_ty actual then []
                    else [FmtErrTypeMismatch dir.fd_position dir.fd_specifier actual]
                  in
                  type_errors @ validate_format_args_aux rest rest_args cfg (arg_idx + 1)

(* Main format validation function for variadic FFI calls *)
let validate_format_call
    (fn_name: string)
    (format_param_idx: nat)
    (directives: list format_directive)
    (variadic_args: list ffi_safe_type)
    (cfg: platform_config)
    : format_analysis_result =
  (* Check for dangerous %n specifiers *)
  let n_warnings = List.Tot.fold_left (fun acc dir ->
    match dir.fd_specifier with
    | FmtWriteCount -> FmtErrDangerousN dir.fd_position :: acc
    | _ -> acc
  ) [] directives in

  (* Check for unbounded %s *)
  let string_warnings = List.Tot.fold_left (fun acc dir ->
    match dir.fd_specifier, dir.fd_precision with
    | FmtString, None -> FmtErrUnboundedString dir.fd_position :: acc
    | _, _ -> acc
  ) [] directives in

  (* Validate argument types and count *)
  let type_errors = validate_format_args_aux directives variadic_args cfg 0 in

  (* Count non-%% directives for expected arg count *)
  let expected_args = List.Tot.fold_left (fun acc dir ->
    match dir.fd_specifier with
    | FmtPercent -> acc
    | _ -> acc + 1
  ) 0 directives in

  {
    far_directives = directives;
    far_arg_count = expected_args;
    far_errors = type_errors;
    far_warnings = n_warnings @ string_warnings
  }

(* Identify printf-family functions *)
let is_printf_family (fn_name: string) : bool =
  fn_name = "printf" || fn_name = "fprintf" || fn_name = "sprintf" ||
  fn_name = "snprintf" || fn_name = "dprintf" ||
  fn_name = "vprintf" || fn_name = "vfprintf" || fn_name = "vsprintf" ||
  fn_name = "vsnprintf" || fn_name = "vdprintf" ||
  (* Wide character versions *)
  fn_name = "wprintf" || fn_name = "fwprintf" || fn_name = "swprintf" ||
  (* Secure versions *)
  fn_name = "printf_s" || fn_name = "fprintf_s" || fn_name = "sprintf_s" ||
  fn_name = "snprintf_s"

(* Get format string parameter index for printf-family functions *)
let get_format_param_index (fn_name: string) : option nat =
  if fn_name = "printf" || fn_name = "vprintf" ||
     fn_name = "wprintf" then Some 0
  else if fn_name = "fprintf" || fn_name = "vfprintf" ||
          fn_name = "fwprintf" || fn_name = "dprintf" || fn_name = "vdprintf" then Some 1
  else if fn_name = "sprintf" || fn_name = "vsprintf" ||
          fn_name = "swprintf" then Some 1
  else if fn_name = "snprintf" || fn_name = "vsnprintf" ||
          fn_name = "snprintf_s" then Some 2
  else if fn_name = "printf_s" then Some 0
  else if fn_name = "fprintf_s" || fn_name = "sprintf_s" then Some 1
  else None

(** ============================================================================
    TYPE REPRESENTATION ATTRIBUTES
    ============================================================================ *)

(* Extended repr attribute for FFI (complements BrrrTypes.repr_attr) *)
type ffi_repr_attr =
  | FReprC           : ffi_repr_attr   (* C-compatible layout *)
  | FReprTransparent : ffi_repr_attr   (* Same layout as single field *)
  | FReprPacked      : ffi_repr_attr   (* No padding between fields *)
  | FReprAlign       : nat -> ffi_repr_attr  (* Minimum alignment *)
  | FReprSimd        : nat -> ffi_repr_attr  (* SIMD-aligned (usually 16 or 32) *)

(* Convert BrrrTypes repr_attr to ffi_repr_attr *)
let repr_to_ffi_repr (r: repr_attr) : option ffi_repr_attr =
  match r with
  | ReprC -> Some FReprC
  | ReprTransparent -> Some FReprTransparent
  | ReprPacked -> Some FReprPacked
  | ReprAlign n -> Some (FReprAlign n)
  | ReprRust -> None  (* Rust repr is not FFI-compatible *)

(* Check if repr is FFI-compatible *)
let is_repr_ffi_compatible (r: repr_attr) : bool =
  match r with
  | ReprC -> true
  | ReprTransparent -> true
  | ReprPacked -> true
  | ReprAlign _ -> true
  | ReprRust -> false

(** ============================================================================
    POINTER OPERATIONS
    ============================================================================ *)

(* Pointer offset calculation *)
let ptr_offset (base_offset: nat) (index: nat) (element_size: nat) : nat =
  base_offset + index * element_size

(* Lemma: pointer offset is commutative in index *)
val ptr_offset_add : base:nat -> i:nat -> j:nat -> size:nat ->
  Lemma (ptr_offset (ptr_offset base i size) j size =
         ptr_offset base (i + j) size)
let ptr_offset_add base i j size = ()

(* Pointer cast safety: check if cast is valid *)
type ptr_cast_kind =
  | PtrCastSafe       : ptr_cast_kind  (* Same size/align, safe *)
  | PtrCastUpcast     : ptr_cast_kind  (* To larger alignment, safe *)
  | PtrCastDowncast   : ptr_cast_kind  (* To smaller alignment, potentially unsafe *)
  | PtrCastReinterpret: ptr_cast_kind  (* Different types, unsafe *)

(* Determine pointer cast kind *)
let classify_ptr_cast (from_ty: ffi_safe_type) (to_ty: ffi_safe_type) : ptr_cast_kind =
  let from_align = ffi_type_align from_ty in
  let to_align = ffi_type_align to_ty in
  if ffi_type_eq from_ty to_ty then PtrCastSafe
  else if to_align <= from_align && to_align > 0 && from_align % to_align = 0 then PtrCastUpcast
  else if from_align < to_align then PtrCastDowncast
  else PtrCastReinterpret

(* Is pointer cast safe without runtime check? *)
let is_ptr_cast_safe (from_ty: ffi_safe_type) (to_ty: ffi_safe_type) : bool =
  match classify_ptr_cast from_ty to_ty with
  | PtrCastSafe -> true
  | PtrCastUpcast -> true
  | _ -> false

(** ============================================================================
    FFI CALL SIGNATURE VALIDATION
    ============================================================================ *)

(* Validate that function parameter types match *)
(* Helper: take first n elements of a list *)
let rec firstn (#a: Type) (n: nat) (l: list a) : Tot (list a) (decreases n) =
  if n = 0 then []
  else match l with
       | [] -> []
       | x :: xs -> x :: firstn (n - 1) xs

(* Validate that function parameter types match *)
let rec validate_params
    (expected: list (string & ffi_safe_type))
    (actual: list ffi_safe_type)
    : bool =
  match expected, actual with
  | [], [] -> true
  | (_, exp_ty) :: exp_rest, act_ty :: act_rest ->
      ffi_type_eq exp_ty act_ty && validate_params exp_rest act_rest
  | _, _ -> false

(* Validate extern function call *)
let validate_ffi_call
    (fn: extern_fn)
    (arg_types: list ffi_safe_type)
    : bool =
  if fn.fn_is_variadic then
    (* Variadic: must have at least the required params *)
    List.Tot.length arg_types >= List.Tot.length fn.fn_params &&
    validate_params fn.fn_params (firstn (List.Tot.length fn.fn_params) arg_types)
  else
    (* Non-variadic: exact match *)
    validate_params fn.fn_params arg_types

(** ============================================================================
    EFFECT ROW FOR FFI
    ============================================================================ *)

(* Effect row for FFI calls *)
let ffi_effect : effect_row = RowExt EFFI RowEmpty

(* Effect row for unsafe FFI calls *)
let unsafe_ffi_effect : effect_row = RowExt EUnsafe (RowExt EFFI RowEmpty)

(* Get effect row for extern function call *)
let extern_fn_effect (fn: extern_fn) : effect_row =
  unsafe_ffi_effect  (* All FFI calls are unsafe *)

(** ============================================================================
    COMMON FFI TYPES
    ============================================================================ *)

(* Standard C types *)
let ffi_c_void : ffi_safe_type = FFIVoid
let ffi_c_char : ffi_safe_type = FFIInt I8 Signed
let ffi_c_uchar : ffi_safe_type = FFIInt I8 Unsigned
let ffi_c_short : ffi_safe_type = FFIInt I16 Signed
let ffi_c_ushort : ffi_safe_type = FFIInt I16 Unsigned
let ffi_c_int : ffi_safe_type = FFIInt I32 Signed
let ffi_c_uint : ffi_safe_type = FFIInt I32 Unsigned
let ffi_c_long : ffi_safe_type = FFIInt I64 Signed  (* Assuming LP64 *)
let ffi_c_ulong : ffi_safe_type = FFIInt I64 Unsigned
let ffi_c_longlong : ffi_safe_type = FFIInt I64 Signed
let ffi_c_ulonglong : ffi_safe_type = FFIInt I64 Unsigned
let ffi_c_float : ffi_safe_type = FFIFloat F32
let ffi_c_double : ffi_safe_type = FFIFloat F64

(* Size types *)
let ffi_size_t : ffi_safe_type = FFIInt I64 Unsigned
let ffi_ssize_t : ffi_safe_type = FFIInt I64 Signed
let ffi_ptrdiff_t : ffi_safe_type = FFIInt I64 Signed
let ffi_intptr_t : ffi_safe_type = FFIInt I64 Signed
let ffi_uintptr_t : ffi_safe_type = FFIInt I64 Unsigned

(** ============================================================================
    EXAMPLE FFI DECLARATIONS
    ============================================================================ *)

(* Example: printf declaration *)
let ffi_printf : extern_fn = {
  fn_name = "printf";
  fn_convention = CC_C;
  fn_params = [("format", FFICStr)];
  fn_return = ffi_c_int;
  fn_is_variadic = true;
  fn_link_name = None
}

(* Example: malloc declaration *)
let ffi_malloc : extern_fn = {
  fn_name = "malloc";
  fn_convention = CC_C;
  fn_params = [("size", ffi_size_t)];
  fn_return = FFIOpaquePtr;
  fn_is_variadic = false;
  fn_link_name = None
}

(* Example: free declaration *)
let ffi_free : extern_fn = {
  fn_name = "free";
  fn_convention = CC_C;
  fn_params = [("ptr", FFIOpaquePtr)];
  fn_return = FFIVoid;
  fn_is_variadic = false;
  fn_link_name = None
}

(** ============================================================================
    VALIDATION LEMMAS
    ============================================================================ *)

(* Lemma: ffi_type_eq is reflexive *)
val ffi_type_eq_refl : t:ffi_safe_type ->
  Lemma (ensures ffi_type_eq t t = true)
        (decreases t)
        [SMTPat (ffi_type_eq t t)]
let rec ffi_type_eq_refl t =
  match t with
  | FFIInt _ _ -> ()
  | FFIFloat _ -> ()
  | FFIPtr inner -> ffi_type_eq_refl inner
  | FFIFnPtr params ret ->
      ffi_type_list_eq_refl params;
      ffi_type_eq_refl ret
  | FFICStr -> ()
  | FFIVoid -> ()
  | FFIStruct fields -> ffi_field_list_eq_refl fields
  | FFIOpaquePtr -> ()

and ffi_type_list_eq_refl (ts: list ffi_safe_type) :
  Lemma (ensures ffi_type_list_eq ts ts = true)
        (decreases ts) =
  match ts with
  | [] -> ()
  | t :: rest -> ffi_type_eq_refl t; ffi_type_list_eq_refl rest

and ffi_field_list_eq_refl (fs: list (string & ffi_safe_type)) :
  Lemma (ensures ffi_field_list_eq fs fs = true)
        (decreases fs) =
  match fs with
  | [] -> ()
  | (_, t) :: rest -> ffi_type_eq_refl t; ffi_field_list_eq_refl rest

(* Lemma: empty param list validates against empty arg list *)
val empty_call_succeeds : fn:extern_fn ->
  Lemma (requires fn.fn_is_variadic = false /\ Nil? fn.fn_params)
        (ensures validate_ffi_call fn [] = true)
let empty_call_succeeds fn = ()

(** ============================================================================
    STRUCT LAYOUT EXAMPLE AND VERIFICATION
    ============================================================================ *)

(* Example: Point struct { i32 x; i32 y; } *)
let point_fields : list (string & ffi_safe_type) =
  [("x", ffi_c_int); ("y", ffi_c_int)]

(* Verify Point layout *)
let point_layout : list field_layout = compute_c_layout point_fields

(* Lemma: Point struct has expected size (8 bytes) *)
val point_size_correct : unit ->
  Lemma (compute_struct_size point_fields = 8)
let point_size_correct () = ()

(* Lemma: Point struct has expected alignment (4 bytes) *)
val point_align_correct : unit ->
  Lemma (compute_struct_align point_fields = 4)
let point_align_correct () = ()

(* Example: Padded struct { i8 a; i32 b; i8 c; } *)
let padded_fields : list (string & ffi_safe_type) =
  [("a", FFIInt I8 Signed); ("b", ffi_c_int); ("c", FFIInt I8 Signed)]

(* Verify padded struct size (should be 12 with C layout: 1+3pad+4+1+3pad) *)
val padded_size_correct : unit ->
  Lemma (compute_struct_size padded_fields = 12)
let padded_size_correct () = ()

(** ============================================================================
    FFI CONTRACT SYSTEM
    ============================================================================

    Based on synthesis_combined.md Section 9.4 (FFI Contracts).
    Implements the VeriFFI-style contract system for verified cross-language calls.

    Key Components:
    - Type mappings between source IR and foreign types
    - Representation requirements (NonNull, Initialized, Aligned, Sized)
    - Preconditions capturing caller obligations
    - Postconditions capturing callee guarantees
    - Ownership transfer semantics
    - Contract verification logic

    Cross-References:
    - Section 7.5: Representation predicates
    - Section 9.1.2: Boundary risk mitigation
    - Section 9.3: Guard generation from contracts
    - Section 12.7: Realizability theorems
    ============================================================================ *)

(** ============================================================================
    TYPE MAPPINGS ACROSS FFI BOUNDARIES
    ============================================================================ *)

(* Language identifier for multi-language FFI *)
type language_id =
  | LangBrrr     : language_id   (* Brrr-Lang (source) *)
  | LangC        : language_id   (* C ABI *)
  | LangRust     : language_id   (* Rust ABI *)
  | LangPython   : language_id   (* Python/CPython ABI *)
  | LangJava     : language_id   (* JNI ABI *)
  | LangGo       : language_id   (* Go cgo ABI *)

(* Foreign type representation for external languages.
   Maps to the concrete representation in the target language. *)
noeq type foreign_type =
  | ForeignInt8     : foreign_type
  | ForeignInt16    : foreign_type
  | ForeignInt32    : foreign_type
  | ForeignInt64    : foreign_type
  | ForeignUInt8    : foreign_type
  | ForeignUInt16   : foreign_type
  | ForeignUInt32   : foreign_type
  | ForeignUInt64   : foreign_type
  | ForeignFloat    : foreign_type   (* float *)
  | ForeignDouble   : foreign_type   (* double *)
  | ForeignBool     : foreign_type
  | ForeignVoid     : foreign_type
  | ForeignPtr      : foreign_type -> foreign_type
  | ForeignCString  : foreign_type   (* null-terminated char* *)
  | ForeignStruct   : string -> foreign_type  (* Named struct *)
  | ForeignOpaque   : string -> foreign_type  (* Opaque handle type *)

(* IR value placeholder - actual values from Values.fst *)
type ir_value = nat  (* Simplified: represents value ID in abstract state *)

(* Foreign value placeholder - represents external value handle *)
type foreign_value = nat

(* Conversion functions between IR and foreign values.
   Used by TMConverted for explicit type conversions. *)
noeq type conversion_fns = {
  convert_fn   : ir_value -> foreign_value;
  unconvert_fn : foreign_value -> option ir_value
}

(* Type mapping describes how values are transformed when crossing FFI boundaries.

   TMDirect:    Same representation in both languages. No conversion needed.
                Example: i32 (Brrr) <-> int (C)

   TMBoxed:     Heap-allocated wrapper around the value.
                Example: Python int <-> boxed arbitrary-precision integer

   TMConverted: Explicit conversion required with convert/unconvert functions.
                Example: Brrr String (UTF-8) <-> Java String (UTF-16)

   TMOpaque:    No access across boundary - treat as opaque handle.
                Example: Python object <-> void* in C *)
noeq type type_mapping =
  | TMDirect    : type_mapping
  | TMBoxed     : type_mapping
  | TMConverted : conversion_fns -> type_mapping
  | TMOpaque    : type_mapping

(* Infer type mapping from IR type to foreign type *)
let infer_type_mapping (src: brrr_type) (tgt: foreign_type) : type_mapping =
  match src, tgt with
  (* Direct integer mappings *)
  | TNumeric (NumInt it), ForeignInt32 ->
      if it.width = I32 && it.sign = Signed then TMDirect else TMConverted {
        convert_fn = (fun v -> v);
        unconvert_fn = (fun v -> Some v)
      }
  | TNumeric (NumInt it), ForeignInt64 ->
      if it.width = I64 && it.sign = Signed then TMDirect else TMOpaque
  (* Float mappings *)
  | TNumeric (NumFloat F32), ForeignFloat -> TMDirect
  | TNumeric (NumFloat F64), ForeignDouble -> TMDirect
  (* Bool mapping *)
  | TPrim PBool, ForeignBool -> TMDirect
  (* Pointer mappings *)
  | TWrap WRaw inner, ForeignPtr _ -> TMDirect
  | TWrap WBox inner, ForeignPtr _ -> TMBoxed
  (* String requires conversion *)
  | TPrim PString, ForeignCString -> TMConverted {
      convert_fn = (fun v -> v);  (* UTF-8 to C string *)
      unconvert_fn = (fun v -> Some v)
    }
  (* Everything else is opaque *)
  | _, _ -> TMOpaque

(** ============================================================================
    REPRESENTATION REQUIREMENTS
    ============================================================================ *)

(* Representation predicate type - placeholder for full dependent type *)
type rep_predicate = nat  (* Simplified: predicate ID *)

(* Representation requirements specify what properties a value must have
   before it can be passed across an FFI boundary.

   RepNonNull:     Pointer must not be null
   RepInitialized: Memory must be fully initialized
   RepAligned:     Memory must be aligned to specified boundary
   RepSized:       Memory must have at least min_size bytes *)
type rep_requirement =
  | RepNonNull      : rep_requirement
  | RepInitialized  : rep_requirement
  | RepAligned      : alignment:nat -> rep_requirement
  | RepSized        : min_size:nat -> rep_requirement
  | RepPredicate    : rep_predicate -> rep_requirement

(* Check if requirement implies another (for subsumption) *)
let rep_requirement_implies (r1 r2: rep_requirement) : bool =
  match r1, r2 with
  | RepNonNull, RepNonNull -> true
  | RepInitialized, RepInitialized -> true
  | RepAligned a1, RepAligned a2 -> a1 >= a2 && a1 % a2 = 0
  | RepSized s1, RepSized s2 -> s1 >= s2
  | RepPredicate p1, RepPredicate p2 -> p1 = p2
  | _, _ -> false

(** ============================================================================
    THREAD SAFETY REQUIREMENTS
    ============================================================================ *)

(* Thread safety requirements for FFI calls.
   Many C libraries have specific threading requirements. *)
type thread_safety_requirement =
  | TSRAnyThread      : thread_safety_requirement  (* Safe from any thread *)
  | TSRSingleThreaded : thread_safety_requirement  (* Not thread-safe *)
  | TSRMainThread     : thread_safety_requirement  (* Must call from main thread *)
  | TSRWithLock       : lock_id -> thread_safety_requirement  (* Must hold lock *)

(* Thread context - current execution context *)
noeq type thread_context = {
  tc_is_main_thread : bool;
  tc_held_locks     : list lock_id;
  tc_thread_id      : nat
}

(* Check if thread context satisfies requirement *)
let thread_context_satisfies (ctx: thread_context) (req: thread_safety_requirement) : bool =
  match req with
  | TSRAnyThread -> true
  | TSRSingleThreaded -> true  (* Caller responsible for single-threading *)
  | TSRMainThread -> ctx.tc_is_main_thread
  | TSRWithLock lid -> List.Tot.mem lid ctx.tc_held_locks

(** ============================================================================
    ACCESS PERMISSIONS
    ============================================================================ *)

(* Access permission levels for ownership requirements *)
type access_permission =
  | APNone      : access_permission   (* No access *)
  | APRead      : access_permission   (* Read-only access *)
  | APWrite     : access_permission   (* Read-write access *)
  | APOwned     : access_permission   (* Full ownership *)

(* Permission ordering: APOwned > APWrite > APRead > APNone *)
let permission_level (p: access_permission) : nat =
  match p with
  | APNone -> 0
  | APRead -> 1
  | APWrite -> 2
  | APOwned -> 3

(* Check if actual permission satisfies required permission *)
let permission_satisfies (actual: access_permission) (required: access_permission) : bool =
  permission_level actual >= permission_level required

(** ============================================================================
    FFI PRECONDITION
    ============================================================================ *)

(* Constraint expression placeholder - represents constraint on a variable *)
type constraint_expr = nat  (* Simplified: constraint ID *)

(* FFI precondition captures all requirements that must hold before the call.

   rep_requirements:       Per-parameter representation predicates
   ownership_requirements: Per-parameter ownership/permission requirements
   value_constraints:      Arbitrary constraints (e.g., x > 0)
   thread_requirements:    Threading model requirement *)
noeq type ffi_precondition = {
  pre_rep_requirements       : list (var_id & rep_requirement);
  pre_ownership_requirements : list (var_id & access_permission);
  pre_value_constraints      : list (var_id & constraint_expr);
  pre_thread_requirements    : option thread_safety_requirement
}

(* Empty precondition - no requirements *)
let empty_precondition : ffi_precondition = {
  pre_rep_requirements = [];
  pre_ownership_requirements = [];
  pre_value_constraints = [];
  pre_thread_requirements = None
}

(* Add representation requirement to precondition *)
let add_rep_requirement (pre: ffi_precondition) (v: var_id) (r: rep_requirement)
    : ffi_precondition =
  { pre with pre_rep_requirements = (v, r) :: pre.pre_rep_requirements }

(* Add ownership requirement to precondition *)
let add_ownership_requirement (pre: ffi_precondition) (v: var_id) (p: access_permission)
    : ffi_precondition =
  { pre with pre_ownership_requirements = (v, p) :: pre.pre_ownership_requirements }

(** ============================================================================
    MEMORY EFFECT SPECIFICATION
    ============================================================================ *)

(* Address type for memory effect specification *)
type address = nat

(* Memory effect specification describes what the callee may do to memory.

   MEUnchanged:     Memory is not modified
   MEModifiedOnly:  Only specified addresses may be modified
   MEMayAllocate:   May allocate new memory
   MEMayFree:       May free specified addresses
   MEArbitrary:     No guarantees - arbitrary memory effects *)
type memory_effect_spec =
  | MEUnchanged     : memory_effect_spec
  | MEModifiedOnly  : list address -> memory_effect_spec
  | MEMayAllocate   : memory_effect_spec
  | MEMayFree       : list address -> memory_effect_spec
  | MEArbitrary     : memory_effect_spec

(* Check if effect spec is pure (no memory effects) *)
let is_pure_effect (e: memory_effect_spec) : bool =
  match e with
  | MEUnchanged -> true
  | _ -> false

(** ============================================================================
    OWNERSHIP TRANSFER SEMANTICS
    ============================================================================ *)

(* Lifetime bound for borrowed references *)
type lifetime_bound =
  | LBStatic : lifetime_bound                (* 'static lifetime *)
  | LBScoped : nat -> lifetime_bound         (* Scoped to depth n *)
  | LBNamed  : string -> lifetime_bound      (* Named lifetime 'a *)

(* Ownership transfer specifies how ownership changes during FFI call.

   OTRetained:    Caller retains ownership
   OTTransferred: Ownership moves to callee (caller must not use after)
   OTBorrowed:    Temporarily borrowed for duration of call
   OTShared:      Shared access granted (no exclusive ownership) *)
type ownership_transfer =
  | OTRetained    : ownership_transfer
  | OTTransferred : ownership_transfer
  | OTBorrowed    : lifetime_bound -> ownership_transfer
  | OTShared      : ownership_transfer

(* Check if ownership transfer is safe (doesn't create dangling references) *)
let ownership_transfer_safe (ot: ownership_transfer) (has_lifetime: bool) : bool =
  match ot with
  | OTRetained -> true
  | OTTransferred -> true
  | OTBorrowed _ -> has_lifetime  (* Must have valid lifetime *)
  | OTShared -> true

(** ============================================================================
    ERROR BEHAVIOR SPECIFICATION
    ============================================================================ *)

(* Error behavior describes how errors are reported across the boundary.

   EBException:   Throws exception of specified type
   EBReturnCode:  Returns error code (e.g., -1, NULL)
   EBSetErrno:    Sets errno global
   EBAbort:       Aborts the process
   EBUndefined:   Undefined behavior on error *)
noeq type error_behavior =
  | EBException  : brrr_type -> error_behavior
  | EBReturnCode : ir_value -> error_behavior
  | EBSetErrno   : error_behavior
  | EBAbort      : error_behavior
  | EBUndefined  : error_behavior

(** ============================================================================
    FFI POSTCONDITION
    ============================================================================ *)

(* FFI postcondition captures guarantees the callee provides.

   return_rep:        Representation requirement on return value
   memory_effects:    What memory operations may have occurred
   ownership_effects: How ownership of each parameter changed
   error_conditions:  Under what conditions errors may occur
   may_trigger_gc:    Whether call may trigger garbage collection *)
noeq type ffi_postcondition = {
  post_return_rep        : rep_requirement;
  post_memory_effects    : memory_effect_spec;
  post_ownership_effects : list (var_id & ownership_transfer);
  post_error_conditions  : list (constraint_expr & error_behavior);
  post_may_trigger_gc    : bool
}

(* Default postcondition - conservative assumptions *)
let default_postcondition : ffi_postcondition = {
  post_return_rep = RepInitialized;
  post_memory_effects = MEArbitrary;
  post_ownership_effects = [];
  post_error_conditions = [];
  post_may_trigger_gc = false
}

(* Pure postcondition - no side effects *)
let pure_postcondition : ffi_postcondition = {
  post_return_rep = RepInitialized;
  post_memory_effects = MEUnchanged;
  post_ownership_effects = [];
  post_error_conditions = [];
  post_may_trigger_gc = false
}

(** ============================================================================
    FFI CONTRACT
    ============================================================================ *)

(* Ownership specification for all parameters *)
noeq type ownership_spec = {
  os_params : list (var_id & ownership_transfer);
  os_return : ownership_transfer
}

(* Default ownership spec - all retained *)
let default_ownership_spec : ownership_spec = {
  os_params = [];
  os_return = OTRetained
}

(* FFI Contract fully specifies the requirements for a cross-language call.

   foreign_function:   Name of the foreign function
   source_language:    Language of the caller
   target_language:    Language of the callee
   param_types:        Type mappings for each parameter
   return_type:        Type mapping for return value
   precondition:       Requirements before call
   postcondition:      Guarantees after call
   ownership_transfer: Ownership semantics
   effect_bounds:      Effect row for the call *)
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

(* Create basic FFI contract with defaults *)
let make_basic_contract
    (name: string)
    (params: list (brrr_type & foreign_type))
    (ret: brrr_type & foreign_type)
    : ffi_contract =
  {
    fc_foreign_function = name;
    fc_source_language = LangBrrr;
    fc_target_language = LangC;
    fc_param_types = List.Tot.map (fun (b, f) -> (b, f, infer_type_mapping b f)) params;
    fc_return_type = (let (b, f) = ret in (b, f, infer_type_mapping b f));
    fc_precondition = empty_precondition;
    fc_postcondition = default_postcondition;
    fc_ownership = default_ownership_spec;
    fc_effect_bounds = unsafe_ffi_effect
  }

(** ============================================================================
    FFI CONTRACT ANNOTATIONS
    ============================================================================ *)

(* Annotations for refining auto-generated contracts.
   These can be extracted from source code attributes or configuration files. *)
type ffi_annotation =
  | AnnNonnull      : var_id -> ffi_annotation        (* Parameter cannot be null *)
  | AnnNullable     : var_id -> ffi_annotation        (* Parameter may be null *)
  | AnnOwned        : var_id -> ffi_annotation        (* Ownership transferred *)
  | AnnBorrowed     : var_id -> ffi_annotation        (* Borrowed reference *)
  | AnnOut          : var_id -> ffi_annotation        (* Output parameter *)
  | AnnInOut        : var_id -> ffi_annotation        (* Input/output parameter *)
  | AnnArraySize    : var_id -> nat -> ffi_annotation (* Array with fixed size *)
  | AnnBufferSize   : var_id -> var_id -> ffi_annotation  (* Buffer sized by param *)
  | AnnMayAllocate  : ffi_annotation                  (* May allocate memory *)
  | AnnMayFree      : ffi_annotation                  (* May free memory *)
  | AnnPure         : ffi_annotation                  (* No side effects *)
  | AnnThreadSafe   : ffi_annotation                  (* Safe for concurrent calls *)

(* Apply annotation to contract *)
let apply_annotation (c: ffi_contract) (ann: ffi_annotation) : ffi_contract =
  match ann with
  | AnnNonnull v ->
      { c with fc_precondition = add_rep_requirement c.fc_precondition v RepNonNull }
  | AnnNullable _ -> c  (* No additional requirement *)
  | AnnOwned v ->
      let new_params = (v, OTTransferred) :: c.fc_ownership.os_params in
      { c with fc_ownership = { c.fc_ownership with os_params = new_params } }
  | AnnBorrowed v ->
      let new_params = (v, OTBorrowed LBStatic) :: c.fc_ownership.os_params in
      { c with fc_ownership = { c.fc_ownership with os_params = new_params } }
  | AnnOut v ->
      { c with fc_precondition = add_ownership_requirement c.fc_precondition v APWrite }
  | AnnInOut v ->
      { c with fc_precondition = add_ownership_requirement c.fc_precondition v APWrite }
  | AnnArraySize v n ->
      { c with fc_precondition = add_rep_requirement c.fc_precondition v (RepSized n) }
  | AnnBufferSize v _ -> c  (* Would need more complex handling *)
  | AnnMayAllocate ->
      { c with fc_postcondition = { c.fc_postcondition with post_memory_effects = MEMayAllocate } }
  | AnnMayFree ->
      { c with fc_postcondition = { c.fc_postcondition with post_memory_effects = MEMayFree [] } }
  | AnnPure ->
      { c with fc_postcondition = pure_postcondition }
  | AnnThreadSafe ->
      { c with fc_precondition = { c.fc_precondition with pre_thread_requirements = Some TSRAnyThread } }

(* Apply list of annotations to contract *)
let rec refine_contract_with_annotations (c: ffi_contract) (anns: list ffi_annotation)
    : ffi_contract =
  match anns with
  | [] -> c
  | ann :: rest -> refine_contract_with_annotations (apply_annotation c ann) rest

(** ============================================================================
    FFI VIOLATION TYPES
    ============================================================================ *)

(* Node ID placeholder for violation locations *)
type violation_node_id = nat

(* FFI violation describes a contract violation detected during verification.

   VRepViolation:          Representation requirement not satisfied
   VOwnershipViolation:    Ownership/permission requirement not satisfied
   VTypeMismatch:          Type mapping mismatch
   VNullViolation:         Null pointer where non-null required
   VUninitializedViolation: Uninitialized memory where initialized required
   VThreadViolation:       Thread safety requirement not satisfied
   VMissingContract:       No contract found for foreign function
   VConversionFailure:     Type conversion failed *)
noeq type ffi_violation =
  | VRepViolation
      : param:var_id
      -> expected:rep_requirement
      -> actual:nat  (* Abstract value representation *)
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

(* Convert violation to string for error reporting *)
let violation_to_string (v: ffi_violation) : string =
  match v with
  | VRepViolation param _ _ -> "Representation violation for parameter " ^ param
  | VOwnershipViolation param _ _ -> "Ownership violation for parameter " ^ param
  | VTypeMismatch _ _ -> "Type mismatch at FFI boundary"
  | VNullViolation param -> "Null pointer violation for parameter " ^ param
  | VUninitializedViolation param -> "Uninitialized memory violation for " ^ param
  | VThreadViolation _ _ -> "Thread safety violation"
  | VMissingContract name -> "Missing FFI contract for function " ^ name
  | VConversionFailure param _ _ -> "Type conversion failed for " ^ param

(** ============================================================================
    ABSTRACT STATE FOR VERIFICATION
    ============================================================================ *)

(* Abstract value representation for verification *)
noeq type abs_value = {
  av_may_be_null        : bool;
  av_may_be_uninitialized : bool;
  av_known_alignment    : option nat;
  av_known_size         : option nat;
  av_permission         : access_permission
}

(* Create unknown abstract value *)
let unknown_abs_value : abs_value = {
  av_may_be_null = true;
  av_may_be_uninitialized = true;
  av_known_alignment = None;
  av_known_size = None;
  av_permission = APNone
}

(* Create concrete abstract value (fully known) *)
let concrete_abs_value (align: nat) (size: nat) (perm: access_permission) : abs_value = {
  av_may_be_null = false;
  av_may_be_uninitialized = false;
  av_known_alignment = Some align;
  av_known_size = Some size;
  av_permission = perm
}

(* Abstract state: mapping from variables to abstract values *)
type abs_state = list (var_id & abs_value)

(* Lookup abstract value for variable *)
let lookup_abs_value (s: abs_state) (v: var_id) : option abs_value =
  List.Tot.assoc v s

(* Empty abstract state *)
let empty_abs_state : abs_state = []

(** ============================================================================
    CONTRACT VERIFICATION
    ============================================================================ *)

(* Check representation requirement against abstract value *)
let check_rep_requirement (av: abs_value) (req: rep_requirement) : option string =
  match req with
  | RepNonNull ->
      if av.av_may_be_null then Some "may be null" else None
  | RepInitialized ->
      if av.av_may_be_uninitialized then Some "may be uninitialized" else None
  | RepAligned align ->
      (match av.av_known_alignment with
       | Some a -> if a % align = 0 then None else Some "misaligned"
       | None -> Some "alignment unknown")
  | RepSized min_size ->
      (match av.av_known_size with
       | Some s -> if s >= min_size then None else Some "too small"
       | None -> Some "size unknown")
  | RepPredicate _ -> None  (* Would need full predicate checking *)

(* Check all representation requirements in precondition *)
let rec check_all_rep_requirements
    (state: abs_state)
    (reqs: list (var_id & rep_requirement))
    : list ffi_violation =
  match reqs with
  | [] -> []
  | (v, req) :: rest ->
      let violations =
        match lookup_abs_value state v with
        | None -> [VRepViolation v req 0]  (* Variable not in state *)
        | Some av ->
            match check_rep_requirement av req with
            | None -> []
            | Some _ ->
                match req with
                | RepNonNull -> [VNullViolation v]
                | RepInitialized -> [VUninitializedViolation v]
                | _ -> [VRepViolation v req 0]
      in
      violations @ check_all_rep_requirements state rest

(* Check all ownership requirements in precondition *)
let rec check_all_ownership_requirements
    (state: abs_state)
    (reqs: list (var_id & access_permission))
    : list ffi_violation =
  match reqs with
  | [] -> []
  | (v, required) :: rest ->
      let violations =
        match lookup_abs_value state v with
        | None -> [VOwnershipViolation v required APNone]
        | Some av ->
            if permission_satisfies av.av_permission required
            then []
            else [VOwnershipViolation v required av.av_permission]
      in
      violations @ check_all_ownership_requirements state rest

(* Check thread safety requirement *)
let check_thread_requirement
    (ctx: thread_context)
    (req: option thread_safety_requirement)
    : list ffi_violation =
  match req with
  | None -> []
  | Some r ->
      if thread_context_satisfies ctx r
      then []
      else [VThreadViolation r ctx]

(* Verification result type *)
noeq type verification_result =
  | VROk     : abs_state -> verification_result
  | VRError  : list ffi_violation -> verification_result

(* Apply postcondition to compute post-state.
   Updates abstract values based on ownership effects. *)
let apply_postcondition
    (state: abs_state)
    (post: ffi_postcondition)
    : abs_state =
  (* Apply ownership effects - mark transferred values as inaccessible *)
  List.Tot.map (fun (v, av) ->
    match List.Tot.assoc v post.post_ownership_effects with
    | Some OTTransferred -> (v, { av with av_permission = APNone })
    | Some OTBorrowed _ -> (v, { av with av_permission = APRead })
    | _ -> (v, av)
  ) state

(* Unsafe context violation - FFI call not in unsafe context *)
type unsafe_context_violation =
  | UCVNotInUnsafe : function_name:string -> unsafe_context_violation
      (* FFI call made outside unsafe block/function *)
  | UCVMissingEffect : function_name:string -> required:unsafe_effect -> unsafe_context_violation
      (* Required unsafe effect not permitted in context *)

(* Check if unsafe context permits FFI call *)
let check_unsafe_context_for_ffi
    (ctx: unsafe_context)
    (fn_name: string)
    : option unsafe_context_violation =
  if is_unsafe_allowed UnsafeFFI ctx then None
  else Some (UCVNotInUnsafe fn_name)

(* Main verification function: verify FFI call against contract.

   Verification steps:
   1. Check unsafe context (FFI calls require unsafe)
   2. Check all representation requirements
   3. Check all ownership requirements
   4. Check thread safety requirements
   5. If all pass, compute post-state via postcondition

   Returns either updated state (success) or list of violations (failure). *)
let verify_ffi_call
    (call_site: violation_node_id)
    (contract: ffi_contract)
    (state: abs_state)
    (thread_ctx: thread_context)
    (unsafe_ctx: unsafe_context)
    : verification_result =
  (* Step 0: Check unsafe context - FFI calls require unsafe *)
  match check_unsafe_context_for_ffi unsafe_ctx contract.fc_foreign_function with
  | Some (UCVNotInUnsafe fn) ->
      VRError [VMissingContract ("unsafe context required for FFI call to " ^ fn)]
  | Some (UCVMissingEffect fn _) ->
      VRError [VMissingContract ("missing unsafe effect for FFI call to " ^ fn)]
  | None ->
      (* Step 1: Check representation requirements *)
      let rep_violations = check_all_rep_requirements state
                             contract.fc_precondition.pre_rep_requirements in

      (* Step 2: Check ownership requirements *)
      let ownership_violations = check_all_ownership_requirements state
                                   contract.fc_precondition.pre_ownership_requirements in

      (* Step 3: Check thread safety *)
      let thread_violations = check_thread_requirement thread_ctx
                                contract.fc_precondition.pre_thread_requirements in

      (* Combine all violations *)
      let all_violations = rep_violations @ ownership_violations @ thread_violations in

      (* Return result *)
      match all_violations with
      | [] -> VROk (apply_postcondition state contract.fc_postcondition)
      | vs -> VRError vs

(* Simplified verification without thread context - requires explicit unsafe *)
let verify_ffi_call_simple
    (contract: ffi_contract)
    (state: abs_state)
    (unsafe_ctx: unsafe_context)
    : verification_result =
  let default_thread_ctx = {
    tc_is_main_thread = true;
    tc_held_locks = [];
    tc_thread_id = 0
  } in
  verify_ffi_call 0 contract state default_thread_ctx unsafe_ctx

(* Verification assuming we are in an unsafe block (for testing/internal use) *)
let verify_ffi_call_in_unsafe
    (contract: ffi_contract)
    (state: abs_state)
    : verification_result =
  verify_ffi_call_simple contract state in_unsafe_block

(** ============================================================================
    CONTRACT DATABASE AND BATCH VERIFICATION
    ============================================================================ *)

(* Contract database: maps function names to contracts *)
type contract_db = list (string & ffi_contract)

(* Lookup contract for function *)
let lookup_contract (db: contract_db) (name: string) : option ffi_contract =
  List.Tot.assoc name db

(* FFI call site representation *)
noeq type ffi_call_site = {
  fcs_node_id   : violation_node_id;
  fcs_func_name : string;
  fcs_state     : abs_state
}

(* Verify all FFI calls in a list against contract database.
   Requires unsafe_context - all FFI calls must be in unsafe context. *)
let rec verify_all_ffi_calls
    (db: contract_db)
    (calls: list ffi_call_site)
    (thread_ctx: thread_context)
    (unsafe_ctx: unsafe_context)
    : list (violation_node_id & ffi_violation) =
  match calls with
  | [] -> []
  | call :: rest ->
      let violations =
        match lookup_contract db call.fcs_func_name with
        | None -> [(call.fcs_node_id, VMissingContract call.fcs_func_name)]
        | Some contract ->
            match verify_ffi_call call.fcs_node_id contract call.fcs_state thread_ctx unsafe_ctx with
            | VROk _ -> []
            | VRError vs -> List.Tot.map (fun v -> (call.fcs_node_id, v)) vs
      in
      violations @ verify_all_ffi_calls db rest thread_ctx unsafe_ctx

(** ============================================================================
    EXAMPLE FFI CONTRACTS
    ============================================================================ *)

(* Contract for malloc: allocates memory, may return null *)
let contract_malloc : ffi_contract = {
  fc_foreign_function = "malloc";
  fc_source_language = LangBrrr;
  fc_target_language = LangC;
  fc_param_types = [(TNumeric (NumInt { width = I64; sign = Unsigned }),
                     ForeignUInt64, TMDirect)];
  fc_return_type = (TWrap WRaw (TPrim PUnit), ForeignPtr ForeignVoid, TMDirect);
  fc_precondition = empty_precondition;
  fc_postcondition = {
    post_return_rep = RepInitialized;  (* Return value is valid pointer or null *)
    post_memory_effects = MEMayAllocate;
    post_ownership_effects = [];
    post_error_conditions = [];
    post_may_trigger_gc = false
  };
  fc_ownership = {
    os_params = [];
    os_return = OTTransferred  (* Caller owns the allocated memory *)
  };
  fc_effect_bounds = unsafe_ffi_effect
}

(* Contract for free: frees memory, takes ownership *)
let contract_free : ffi_contract = {
  fc_foreign_function = "free";
  fc_source_language = LangBrrr;
  fc_target_language = LangC;
  fc_param_types = [(TWrap WRaw (TPrim PUnit), ForeignPtr ForeignVoid, TMDirect)];
  fc_return_type = (TPrim PUnit, ForeignVoid, TMDirect);
  fc_precondition = {
    pre_rep_requirements = [("ptr", RepNonNull)];  (* Can be null per C spec, but we require non-null *)
    pre_ownership_requirements = [("ptr", APOwned)];
    pre_value_constraints = [];
    pre_thread_requirements = None
  };
  fc_postcondition = {
    post_return_rep = RepInitialized;
    post_memory_effects = MEMayFree [];
    post_ownership_effects = [("ptr", OTTransferred)];  (* Ownership consumed *)
    post_error_conditions = [];
    post_may_trigger_gc = false
  };
  fc_ownership = {
    os_params = [("ptr", OTTransferred)];
    os_return = OTRetained
  };
  fc_effect_bounds = unsafe_ffi_effect
}

(* Contract for strlen: reads C string, borrowed access *)
let contract_strlen : ffi_contract = {
  fc_foreign_function = "strlen";
  fc_source_language = LangBrrr;
  fc_target_language = LangC;
  fc_param_types = [(TPrim PString, ForeignCString, TMConverted {
    convert_fn = (fun v -> v);
    unconvert_fn = (fun v -> Some v)
  })];
  fc_return_type = (TNumeric (NumInt { width = I64; sign = Unsigned }),
                    ForeignUInt64, TMDirect);
  fc_precondition = {
    pre_rep_requirements = [("s", RepNonNull); ("s", RepInitialized)];
    pre_ownership_requirements = [("s", APRead)];
    pre_value_constraints = [];
    pre_thread_requirements = Some TSRAnyThread  (* Thread-safe *)
  };
  fc_postcondition = pure_postcondition;  (* Pure function *)
  fc_ownership = {
    os_params = [("s", OTBorrowed LBStatic)];
    os_return = OTRetained
  };
  fc_effect_bounds = ffi_effect  (* Not unsafe since it's read-only *)
}

(** ============================================================================
    VERIFICATION LEMMAS
    ============================================================================ *)

(* Lemma: empty precondition always passes *)
val empty_precondition_passes : state:abs_state ->
  Lemma (check_all_rep_requirements state [] = [] /\
         check_all_ownership_requirements state [] = [])
let empty_precondition_passes state = ()

(* Lemma: permission_satisfies is reflexive *)
val permission_satisfies_refl : p:access_permission ->
  Lemma (permission_satisfies p p = true)
        [SMTPat (permission_satisfies p p)]
let permission_satisfies_refl p = ()

(* Lemma: permission_satisfies is transitive *)
val permission_satisfies_trans : p1:access_permission -> p2:access_permission ->
                                 p3:access_permission ->
  Lemma (requires permission_satisfies p1 p2 = true /\
                  permission_satisfies p2 p3 = true)
        (ensures permission_satisfies p1 p3 = true)
let permission_satisfies_trans p1 p2 p3 = ()

(* Lemma: owned permission satisfies all permissions *)
val owned_satisfies_all : p:access_permission ->
  Lemma (permission_satisfies APOwned p = true)
let owned_satisfies_all p = ()

(* Lemma: concrete abstract value with proper alignment satisfies aligned requirement *)
val concrete_satisfies_aligned : align:nat -> size:nat -> perm:access_permission ->
  Lemma (requires align > 0)
        (ensures check_rep_requirement (concrete_abs_value align size perm)
                                       (RepAligned align) = None)
let concrete_satisfies_aligned align size perm = ()

(* Lemma: concrete abstract value with proper size satisfies sized requirement *)
val concrete_satisfies_sized : align:nat -> size:nat -> perm:access_permission ->
  Lemma (check_rep_requirement (concrete_abs_value align size perm)
                               (RepSized size) = None)
let concrete_satisfies_sized align size perm = ()

(** ============================================================================
    ABI COMPATIBILITY CHECKING SYSTEM
    ============================================================================

    Brrr-Machine Cross-Platform ABI Analysis

    This module provides comprehensive ABI compatibility checking for cross-platform
    and cross-language code analysis. Key capabilities:

    1. ENDIANNESS TRACKING
       - Detect byte order mismatches in network protocols
       - Flag cross-platform data serialization issues

    2. TARGET ABI CONFIGURATION
       - Architecture (x86, x64, ARM, ARM64, RISC-V)
       - Operating system (Linux, Windows, macOS, FreeBSD)
       - Pointer width and integer type sizes
       - Struct packing and calling conventions

    3. LAYOUT COMPUTATION
       - Per-platform struct layout calculation
       - Field offset computation with padding
       - Alignment verification

    4. ABI MISMATCH DETECTION
       - SizeMismatch: Total struct size differs
       - AlignmentMismatch: Field alignment differs
       - OffsetMismatch: Field position differs (padding difference)
       - TypeWidthMismatch: Same field has different size

    5. PLATFORM DATABASE
       - Predefined configurations for common platforms
       - Linux x64, Windows x64, macOS ARM64, etc.

    Cross-References:
    - synthesis_combined.md Section "Gap 4: ABI Compatibility Checking"
    - Section 9.1.2: Boundary risk mitigation
    - Section 7.5: Representation predicates
    ============================================================================ *)

(** ============================================================================
    ENDIANNESS
    ============================================================================ *)

(* Endianness affects multi-byte value interpretation.
   Critical for network protocols and cross-platform data exchange. *)
type endianness =
  | BigEndian    : endianness   (* MSB first - network byte order *)
  | LittleEndian : endianness   (* LSB first - x86, ARM default *)

(* Convert endianness to string *)
let endianness_to_string (e: endianness) : string =
  match e with
  | BigEndian -> "big-endian"
  | LittleEndian -> "little-endian"

(* Check if byte swap is needed between two endiannesses *)
let needs_byte_swap (source: endianness) (target: endianness) : bool =
  match source, target with
  | BigEndian, LittleEndian -> true
  | LittleEndian, BigEndian -> true
  | _, _ -> false

(** ============================================================================
    TARGET ARCHITECTURE
    ============================================================================ *)

(* CPU architecture identifier.
   Each architecture has specific register sizes, calling conventions,
   and alignment requirements. *)
type arch =
  | Arch_x86     : arch   (* 32-bit x86 (IA-32) *)
  | Arch_x86_64  : arch   (* 64-bit x86 (AMD64/Intel 64) *)
  | Arch_ARM32   : arch   (* 32-bit ARM (ARMv7 and earlier) *)
  | Arch_ARM64   : arch   (* 64-bit ARM (AArch64/ARMv8+) *)
  | Arch_RISCV32 : arch   (* 32-bit RISC-V *)
  | Arch_RISCV64 : arch   (* 64-bit RISC-V *)
  | Arch_WASM32  : arch   (* WebAssembly 32-bit *)
  | Arch_WASM64  : arch   (* WebAssembly 64-bit (memory64) *)

(* Convert architecture to string *)
let arch_to_string (a: arch) : string =
  match a with
  | Arch_x86 -> "x86"
  | Arch_x86_64 -> "x86_64"
  | Arch_ARM32 -> "arm"
  | Arch_ARM64 -> "aarch64"
  | Arch_RISCV32 -> "riscv32"
  | Arch_RISCV64 -> "riscv64"
  | Arch_WASM32 -> "wasm32"
  | Arch_WASM64 -> "wasm64"

(* Get pointer size for architecture (in bytes) *)
let arch_pointer_size (a: arch) : nat =
  match a with
  | Arch_x86 -> 4
  | Arch_x86_64 -> 8
  | Arch_ARM32 -> 4
  | Arch_ARM64 -> 8
  | Arch_RISCV32 -> 4
  | Arch_RISCV64 -> 8
  | Arch_WASM32 -> 4
  | Arch_WASM64 -> 8

(* Get default endianness for architecture *)
let arch_default_endianness (a: arch) : endianness =
  (* Most modern architectures are little-endian by default.
     ARM and RISC-V can be configured either way but default to little. *)
  match a with
  | Arch_x86 -> LittleEndian
  | Arch_x86_64 -> LittleEndian
  | Arch_ARM32 -> LittleEndian
  | Arch_ARM64 -> LittleEndian
  | Arch_RISCV32 -> LittleEndian
  | Arch_RISCV64 -> LittleEndian
  | Arch_WASM32 -> LittleEndian
  | Arch_WASM64 -> LittleEndian

(** ============================================================================
    TARGET OPERATING SYSTEM
    ============================================================================ *)

(* Operating system identifier.
   OS affects ABI through:
   - Calling conventions (Windows vs System V)
   - Struct packing defaults
   - Long integer size (LLP64 vs LP64)
   - TLS implementation *)
type target_os =
  | OS_Linux   : target_os
  | OS_Windows : target_os
  | OS_MacOS   : target_os
  | OS_FreeBSD : target_os
  | OS_iOS     : target_os
  | OS_Android : target_os
  | OS_WASI    : target_os   (* WebAssembly System Interface *)
  | OS_None    : target_os   (* Bare metal / no OS *)

(* Convert OS to string *)
let os_to_string (o: target_os) : string =
  match o with
  | OS_Linux -> "linux"
  | OS_Windows -> "windows"
  | OS_MacOS -> "macos"
  | OS_FreeBSD -> "freebsd"
  | OS_iOS -> "ios"
  | OS_Android -> "android"
  | OS_WASI -> "wasi"
  | OS_None -> "none"

(* Is this OS POSIX-like? (affects certain ABI aspects) *)
let is_posix_like (o: target_os) : bool =
  match o with
  | OS_Linux -> true
  | OS_MacOS -> true
  | OS_FreeBSD -> true
  | OS_iOS -> true
  | OS_Android -> true
  | OS_WASI -> true
  | OS_Windows -> false
  | OS_None -> false

(** ============================================================================
    PACKING MODE
    ============================================================================ *)

(* Struct packing mode affects field alignment and padding.

   PackDefault:  Platform default padding for alignment
   PackPacked:   No padding (#pragma pack(1), __attribute__((packed)))
   PackAlign:    Explicit alignment override (#pragma pack(n))
   PackExplicit: Padding fields are explicit in the struct *)
type packing_mode =
  | PackDefault  : packing_mode
  | PackPacked   : packing_mode
  | PackAlign    : alignment:nat -> packing_mode
  | PackExplicit : packing_mode

(* Convert packing mode to string *)
let packing_mode_to_string (p: packing_mode) : string =
  match p with
  | PackDefault -> "default"
  | PackPacked -> "packed"
  | PackAlign n -> "pack(" ^ string_of_int n ^ ")"
  | PackExplicit -> "explicit"

(** ============================================================================
    LAYOUT INFO
    ============================================================================ *)

(* Physical memory layout information for a type.
   Captures the concrete representation in memory. *)
noeq type layout_info = {
  li_size      : nat;        (* Total size in bytes *)
  li_alignment : nat;        (* Required alignment in bytes *)
  li_endianness: endianness  (* Byte order for multi-byte values *)
}

(* Create layout info *)
let make_layout_info (size: nat) (align: nat) (endian: endianness) : layout_info = {
  li_size = size;
  li_alignment = align;
  li_endianness = endian
}

(* Check if layout_info values are compatible (same size and alignment) *)
let layout_info_compatible (l1 l2: layout_info) : bool =
  l1.li_size = l2.li_size &&
  l1.li_alignment = l2.li_alignment

(* Check if layouts are exactly equal *)
let layout_info_eq (l1 l2: layout_info) : bool =
  l1.li_size = l2.li_size &&
  l1.li_alignment = l2.li_alignment &&
  (match l1.li_endianness, l2.li_endianness with
   | BigEndian, BigEndian -> true
   | LittleEndian, LittleEndian -> true
   | _, _ -> false)

(** ============================================================================
    TARGET ABI CONFIGURATION
    ============================================================================ *)

(* Complete target ABI specification.
   Captures all platform-specific information needed for correct
   memory layout computation and FFI boundary checking. *)
noeq type target_abi = {
  abi_arch           : arch;              (* Target architecture *)
  abi_os             : target_os;         (* Target operating system *)
  abi_endianness     : endianness;        (* Byte order *)
  abi_pointer_size   : nat;               (* Pointer width in bytes (4 or 8) *)
  abi_i8_size        : nat;               (* i8/char size (always 1) *)
  abi_i16_size       : nat;               (* i16/short size (always 2) *)
  abi_i32_size       : nat;               (* i32/int size (always 4) *)
  abi_i64_size       : nat;               (* i64/long long size (always 8) *)
  abi_i128_size      : nat;               (* i128 size (16, or emulated) *)
  abi_long_size      : nat;               (* C 'long' size (4 on Windows, 8 on LP64) *)
  abi_size_t_size    : nat;               (* size_t size (pointer width) *)
  abi_f32_size       : nat;               (* f32/float size (always 4) *)
  abi_f64_size       : nat;               (* f64/double size (always 8) *)
  abi_max_align      : nat;               (* Maximum natural alignment *)
  abi_packing        : packing_mode;      (* Default struct packing *)
  abi_calling_conv   : calling_convention (* Default calling convention *)
}

(* Get ABI name for display *)
let abi_to_string (abi: target_abi) : string =
  arch_to_string abi.abi_arch ^ "-" ^ os_to_string abi.abi_os

(* Get integer width size for this ABI *)
let abi_int_width_size (abi: target_abi) (w: int_width) : nat =
  match w with
  | I8 -> abi.abi_i8_size
  | I16 -> abi.abi_i16_size
  | I32 -> abi.abi_i32_size
  | I64 -> abi.abi_i64_size
  | I128 -> abi.abi_i128_size
  | IBig -> abi.abi_pointer_size  (* BigInt is pointer to heap *)

(* Get float precision size for this ABI *)
let abi_float_prec_size (abi: target_abi) (p: float_prec) : nat =
  match p with
  | F16 -> 2
  | F32 -> abi.abi_f32_size
  | F64 -> abi.abi_f64_size

(** ============================================================================
    PLATFORM DATABASE
    ============================================================================

    Predefined ABI configurations for common platforms.
    These capture the actual ABI conventions used by each platform. *)

(* Linux x86_64 (LP64 ABI - System V AMD64 ABI) *)
let abi_linux_x86_64 : target_abi = {
  abi_arch = Arch_x86_64;
  abi_os = OS_Linux;
  abi_endianness = LittleEndian;
  abi_pointer_size = 8;
  abi_i8_size = 1;
  abi_i16_size = 2;
  abi_i32_size = 4;
  abi_i64_size = 8;
  abi_i128_size = 16;
  abi_long_size = 8;           (* LP64: long is 8 bytes *)
  abi_size_t_size = 8;
  abi_f32_size = 4;
  abi_f64_size = 8;
  abi_max_align = 16;          (* SSE requires 16-byte alignment *)
  abi_packing = PackDefault;
  abi_calling_conv = CC_C
}

(* Linux x86 (ILP32 ABI) *)
let abi_linux_x86 : target_abi = {
  abi_arch = Arch_x86;
  abi_os = OS_Linux;
  abi_endianness = LittleEndian;
  abi_pointer_size = 4;
  abi_i8_size = 1;
  abi_i16_size = 2;
  abi_i32_size = 4;
  abi_i64_size = 8;
  abi_i128_size = 16;
  abi_long_size = 4;           (* ILP32: long is 4 bytes *)
  abi_size_t_size = 4;
  abi_f32_size = 4;
  abi_f64_size = 8;
  abi_max_align = 8;           (* No SSE requirement by default *)
  abi_packing = PackDefault;
  abi_calling_conv = CC_C
}

(* Windows x86_64 (LLP64 ABI - Microsoft x64) *)
let abi_windows_x86_64 : target_abi = {
  abi_arch = Arch_x86_64;
  abi_os = OS_Windows;
  abi_endianness = LittleEndian;
  abi_pointer_size = 8;
  abi_i8_size = 1;
  abi_i16_size = 2;
  abi_i32_size = 4;
  abi_i64_size = 8;
  abi_i128_size = 16;
  abi_long_size = 4;           (* LLP64: long is 4 bytes on Windows! *)
  abi_size_t_size = 8;
  abi_f32_size = 4;
  abi_f64_size = 8;
  abi_max_align = 16;
  abi_packing = PackDefault;
  abi_calling_conv = CC_System  (* Windows uses its own convention *)
}

(* Windows x86 (ILP32 ABI) *)
let abi_windows_x86 : target_abi = {
  abi_arch = Arch_x86;
  abi_os = OS_Windows;
  abi_endianness = LittleEndian;
  abi_pointer_size = 4;
  abi_i8_size = 1;
  abi_i16_size = 2;
  abi_i32_size = 4;
  abi_i64_size = 8;
  abi_i128_size = 16;
  abi_long_size = 4;
  abi_size_t_size = 4;
  abi_f32_size = 4;
  abi_f64_size = 8;
  abi_max_align = 8;
  abi_packing = PackDefault;
  abi_calling_conv = CC_System
}

(* macOS x86_64 (LP64 ABI - System V AMD64 ABI variant) *)
let abi_macos_x86_64 : target_abi = {
  abi_arch = Arch_x86_64;
  abi_os = OS_MacOS;
  abi_endianness = LittleEndian;
  abi_pointer_size = 8;
  abi_i8_size = 1;
  abi_i16_size = 2;
  abi_i32_size = 4;
  abi_i64_size = 8;
  abi_i128_size = 16;
  abi_long_size = 8;
  abi_size_t_size = 8;
  abi_f32_size = 4;
  abi_f64_size = 8;
  abi_max_align = 16;
  abi_packing = PackDefault;
  abi_calling_conv = CC_C
}

(* macOS ARM64 (LP64 ABI - Apple Silicon) *)
let abi_macos_arm64 : target_abi = {
  abi_arch = Arch_ARM64;
  abi_os = OS_MacOS;
  abi_endianness = LittleEndian;
  abi_pointer_size = 8;
  abi_i8_size = 1;
  abi_i16_size = 2;
  abi_i32_size = 4;
  abi_i64_size = 8;
  abi_i128_size = 16;
  abi_long_size = 8;
  abi_size_t_size = 8;
  abi_f32_size = 4;
  abi_f64_size = 8;
  abi_max_align = 16;          (* NEON requires 16-byte alignment *)
  abi_packing = PackDefault;
  abi_calling_conv = CC_C
}

(* Linux ARM64 (LP64 ABI - AAPCS64) *)
let abi_linux_arm64 : target_abi = {
  abi_arch = Arch_ARM64;
  abi_os = OS_Linux;
  abi_endianness = LittleEndian;
  abi_pointer_size = 8;
  abi_i8_size = 1;
  abi_i16_size = 2;
  abi_i32_size = 4;
  abi_i64_size = 8;
  abi_i128_size = 16;
  abi_long_size = 8;
  abi_size_t_size = 8;
  abi_f32_size = 4;
  abi_f64_size = 8;
  abi_max_align = 16;
  abi_packing = PackDefault;
  abi_calling_conv = CC_C
}

(* Linux ARM32 (ILP32 ABI - AAPCS) *)
let abi_linux_arm32 : target_abi = {
  abi_arch = Arch_ARM32;
  abi_os = OS_Linux;
  abi_endianness = LittleEndian;
  abi_pointer_size = 4;
  abi_i8_size = 1;
  abi_i16_size = 2;
  abi_i32_size = 4;
  abi_i64_size = 8;
  abi_i128_size = 16;
  abi_long_size = 4;
  abi_size_t_size = 4;
  abi_f32_size = 4;
  abi_f64_size = 8;
  abi_max_align = 8;
  abi_packing = PackDefault;
  abi_calling_conv = CC_C
}

(* WebAssembly 32-bit (wasm32-unknown-unknown) *)
let abi_wasm32 : target_abi = {
  abi_arch = Arch_WASM32;
  abi_os = OS_None;
  abi_endianness = LittleEndian;
  abi_pointer_size = 4;
  abi_i8_size = 1;
  abi_i16_size = 2;
  abi_i32_size = 4;
  abi_i64_size = 8;
  abi_i128_size = 16;
  abi_long_size = 4;
  abi_size_t_size = 4;
  abi_f32_size = 4;
  abi_f64_size = 8;
  abi_max_align = 8;
  abi_packing = PackDefault;
  abi_calling_conv = CC_C
}

(* Android ARM64 (LP64 ABI) *)
let abi_android_arm64 : target_abi = {
  abi_arch = Arch_ARM64;
  abi_os = OS_Android;
  abi_endianness = LittleEndian;
  abi_pointer_size = 8;
  abi_i8_size = 1;
  abi_i16_size = 2;
  abi_i32_size = 4;
  abi_i64_size = 8;
  abi_i128_size = 16;
  abi_long_size = 8;
  abi_size_t_size = 8;
  abi_f32_size = 4;
  abi_f64_size = 8;
  abi_max_align = 16;
  abi_packing = PackDefault;
  abi_calling_conv = CC_C
}

(* iOS ARM64 (LP64 ABI) *)
let abi_ios_arm64 : target_abi = {
  abi_arch = Arch_ARM64;
  abi_os = OS_iOS;
  abi_endianness = LittleEndian;
  abi_pointer_size = 8;
  abi_i8_size = 1;
  abi_i16_size = 2;
  abi_i32_size = 4;
  abi_i64_size = 8;
  abi_i128_size = 16;
  abi_long_size = 8;
  abi_size_t_size = 8;
  abi_f32_size = 4;
  abi_f64_size = 8;
  abi_max_align = 16;
  abi_packing = PackDefault;
  abi_calling_conv = CC_C
}

(* Get predefined ABI for a target triple.
   Returns None if the combination is not predefined. *)
let get_predefined_abi (a: arch) (o: target_os) : option target_abi =
  match a, o with
  | Arch_x86_64, OS_Linux -> Some abi_linux_x86_64
  | Arch_x86, OS_Linux -> Some abi_linux_x86
  | Arch_x86_64, OS_Windows -> Some abi_windows_x86_64
  | Arch_x86, OS_Windows -> Some abi_windows_x86
  | Arch_x86_64, OS_MacOS -> Some abi_macos_x86_64
  | Arch_ARM64, OS_MacOS -> Some abi_macos_arm64
  | Arch_ARM64, OS_Linux -> Some abi_linux_arm64
  | Arch_ARM32, OS_Linux -> Some abi_linux_arm32
  | Arch_WASM32, OS_None -> Some abi_wasm32
  | Arch_ARM64, OS_Android -> Some abi_android_arm64
  | Arch_ARM64, OS_iOS -> Some abi_ios_arm64
  | _, _ -> None

(** ============================================================================
    ABI MISMATCH TYPES
    ============================================================================

    Types of ABI incompatibilities that can cause memory corruption
    or undefined behavior when crossing FFI boundaries. *)

(* ABI mismatch diagnostic information.
   Each variant captures a specific type of ABI incompatibility. *)
type abi_mismatch =
  | SizeMismatch
      : expected:nat
      -> actual:nat
      -> abi_mismatch
      (* Total struct size differs between source and target.
         Example: sizeof(Data) = 8 on Windows, 16 on Linux. *)

  | AlignmentMismatch
      : field:string
      -> expected:nat
      -> actual:nat
      -> abi_mismatch
      (* Field alignment requirement differs.
         Can cause unaligned access faults on strict architectures. *)

  | OffsetMismatch
      : field:string
      -> expected:nat
      -> actual:nat
      -> abi_mismatch
      (* Field starts at different positions due to padding differences.
         Reading field from wrong offset causes data corruption. *)

  | TypeWidthMismatch
      : field:string
      -> expected:nat
      -> actual:nat
      -> abi_mismatch
      (* Same field name has different sizes.
         Example: 'long' is 4 bytes on Windows x64, 8 on Linux x64. *)

  | EndiannessMismatch
      : field:string
      -> source:endianness
      -> target:endianness
      -> abi_mismatch
      (* Multi-byte field has different byte order.
         Requires explicit byte swap for correct interpretation. *)

  | FieldCountMismatch
      : expected:nat
      -> actual:nat
      -> abi_mismatch
      (* Struct has different number of fields.
         Likely indicates mismatched struct definitions. *)

  | FieldNameMismatch
      : index:nat
      -> expected:string
      -> actual:string
      -> abi_mismatch
      (* Field at same index has different names.
         May indicate struct definition mismatch or versioning issue. *)

(* Convert ABI mismatch to human-readable string *)
let abi_mismatch_to_string (m: abi_mismatch) : string =
  match m with
  | SizeMismatch exp act ->
      "Size mismatch: expected " ^ string_of_int exp ^
      " bytes, actual " ^ string_of_int act ^ " bytes"
  | AlignmentMismatch field exp act ->
      "Alignment mismatch for field '" ^ field ^
      "': expected " ^ string_of_int exp ^
      " bytes, actual " ^ string_of_int act ^ " bytes"
  | OffsetMismatch field exp act ->
      "Offset mismatch for field '" ^ field ^
      "': expected offset " ^ string_of_int exp ^
      ", actual offset " ^ string_of_int act
  | TypeWidthMismatch field exp act ->
      "Type width mismatch for field '" ^ field ^
      "': expected " ^ string_of_int exp ^
      " bytes, actual " ^ string_of_int act ^ " bytes"
  | EndiannessMismatch field src tgt ->
      "Endianness mismatch for field '" ^ field ^
      "': source is " ^ endianness_to_string src ^
      ", target is " ^ endianness_to_string tgt
  | FieldCountMismatch exp act ->
      "Field count mismatch: expected " ^ string_of_int exp ^
      " fields, actual " ^ string_of_int act ^ " fields"
  | FieldNameMismatch idx exp act ->
      "Field name mismatch at index " ^ string_of_int idx ^
      ": expected '" ^ exp ^ "', actual '" ^ act ^ "'"

(* Severity level for ABI mismatches *)
type mismatch_severity =
  | SeverityCritical : mismatch_severity  (* Will cause crash or corruption *)
  | SeverityHigh     : mismatch_severity  (* Likely to cause issues *)
  | SeverityMedium   : mismatch_severity  (* May cause issues in edge cases *)
  | SeverityLow      : mismatch_severity  (* Informational *)

(* Get severity for an ABI mismatch *)
let mismatch_severity (m: abi_mismatch) : mismatch_severity =
  match m with
  | SizeMismatch _ _ -> SeverityCritical      (* Struct size wrong = memory corruption *)
  | OffsetMismatch _ _ _ -> SeverityCritical  (* Wrong field position = data corruption *)
  | TypeWidthMismatch _ _ _ -> SeverityHigh   (* Field size wrong = potential overflow *)
  | AlignmentMismatch _ _ _ -> SeverityHigh   (* May cause SIGBUS on strict arch *)
  | EndiannessMismatch _ _ _ -> SeverityMedium (* Data readable but wrong value *)
  | FieldCountMismatch _ _ -> SeverityCritical (* Likely wrong struct definition *)
  | FieldNameMismatch _ _ _ -> SeverityLow     (* May be intentional rename *)

(** ============================================================================
    IR STRUCT WITH LAYOUT METADATA
    ============================================================================

    Extended struct representation that includes explicit layout information.
    This allows comparing structs across different ABIs. *)

(* Field with explicit offset information *)
noeq type ir_field = {
  irf_name   : string;           (* Field name *)
  irf_type   : ffi_safe_type;    (* Field type *)
  irf_offset : nat;              (* Byte offset from struct start *)
  irf_size   : nat;              (* Field size in bytes *)
  irf_align  : nat               (* Field alignment requirement *)
}

(* IR struct with full layout metadata *)
noeq type ir_struct = {
  irs_name   : string;           (* Struct name *)
  irs_fields : list ir_field;    (* Fields with offsets *)
  irs_layout : layout_info;      (* Overall layout *)
  irs_abi    : target_abi        (* ABI used for layout calculation *)
}

(** ============================================================================
    ABI-AWARE LAYOUT COMPUTATION
    ============================================================================

    Compute struct layout according to a specific target ABI.
    This accounts for:
    - Platform-specific type sizes (e.g., 'long' on Windows vs Linux)
    - Alignment requirements and padding
    - Packing directives *)

(* Get size of FFI type under a specific ABI *)
let rec ffi_type_size_abi (abi: target_abi) (t: ffi_safe_type) : Tot nat (decreases t) =
  match t with
  | FFIInt w _ -> abi_int_width_size abi w
  | FFIFloat p -> abi_float_prec_size abi p
  | FFIPtr _ -> abi.abi_pointer_size
  | FFIFnPtr _ _ -> abi.abi_pointer_size
  | FFICStr -> abi.abi_pointer_size
  | FFIVoid -> 0
  | FFIOpaquePtr -> abi.abi_pointer_size
  | FFIStruct fields -> compute_struct_size_abi abi fields

(* Get alignment of FFI type under a specific ABI *)
and ffi_type_align_abi (abi: target_abi) (t: ffi_safe_type) : Tot nat (decreases t) =
  match t with
  | FFIInt w _ -> abi_int_width_size abi w
  | FFIFloat p -> abi_float_prec_size abi p
  | FFIPtr _ -> abi.abi_pointer_size
  | FFIFnPtr _ _ -> abi.abi_pointer_size
  | FFICStr -> abi.abi_pointer_size
  | FFIVoid -> 1
  | FFIOpaquePtr -> abi.abi_pointer_size
  | FFIStruct fields -> compute_struct_align_abi abi fields

(* Compute struct alignment for given ABI (max of field alignments) *)
and compute_struct_align_abi (abi: target_abi) (fields: list (string & ffi_safe_type))
    : Tot nat (decreases fields) =
  match fields with
  | [] -> 1
  | (_, t) :: rest ->
      let field_align = ffi_type_align_abi abi t in
      let rest_align = compute_struct_align_abi abi rest in
      if field_align >= rest_align then field_align else rest_align

(* Compute struct size with ABI-specific padding *)
and compute_struct_size_abi (abi: target_abi) (fields: list (string & ffi_safe_type))
    : Tot nat (decreases fields) =
  compute_struct_size_abi_aux abi fields 0 1

(* Auxiliary function for struct size computation with accumulator *)
and compute_struct_size_abi_aux
    (abi: target_abi)
    (fields: list (string & ffi_safe_type))
    (current_offset: nat)
    (max_align: nat)
    : Tot nat (decreases fields) =
  match fields with
  | [] -> align_up current_offset max_align
  | (_, t) :: rest ->
      let field_size = ffi_type_size_abi abi t in
      let field_align =
        match abi.abi_packing with
        | PackPacked -> 1  (* No alignment padding *)
        | PackAlign n -> if n < ffi_type_align_abi abi t then n else ffi_type_align_abi abi t
        | _ -> ffi_type_align_abi abi t
      in
      let new_max_align = if field_align > max_align then field_align else max_align in
      let aligned_offset = align_up current_offset field_align in
      let next_offset = aligned_offset + field_size in
      compute_struct_size_abi_aux abi rest next_offset new_max_align

(* Compute full field layout for struct under given ABI *)
let rec compute_layout_abi_aux
    (abi: target_abi)
    (fields: list (string & ffi_safe_type))
    (current_offset: nat)
    : Tot (list ir_field) (decreases fields) =
  match fields with
  | [] -> []
  | (name, t) :: rest ->
      let field_size = ffi_type_size_abi abi t in
      let field_align =
        match abi.abi_packing with
        | PackPacked -> 1
        | PackAlign n -> if n < ffi_type_align_abi abi t then n else ffi_type_align_abi abi t
        | _ -> ffi_type_align_abi abi t
      in
      let aligned_offset = align_up current_offset field_align in
      let field = {
        irf_name = name;
        irf_type = t;
        irf_offset = aligned_offset;
        irf_size = field_size;
        irf_align = field_align
      } in
      field :: compute_layout_abi_aux abi rest (aligned_offset + field_size)

(* Compute struct with full layout under given ABI *)
let compute_struct_layout_for_abi
    (name: string)
    (fields: list (string & ffi_safe_type))
    (abi: target_abi)
    : ir_struct =
  let ir_fields = compute_layout_abi_aux abi fields 0 in
  let total_size = compute_struct_size_abi abi fields in
  let struct_align = compute_struct_align_abi abi fields in
  {
    irs_name = name;
    irs_fields = ir_fields;
    irs_layout = {
      li_size = total_size;
      li_alignment = struct_align;
      li_endianness = abi.abi_endianness
    };
    irs_abi = abi
  }

(** ============================================================================
    ABI COMPATIBILITY CHECKING
    ============================================================================

    Main function to detect ABI incompatibilities between source and target
    struct representations. This is critical for FFI boundary safety. *)

(* Compare two field lists for mismatches *)
let rec compare_fields
    (source_fields: list ir_field)
    (target_fields: list ir_field)
    (source_endian: endianness)
    (target_endian: endianness)
    : list abi_mismatch =
  match source_fields, target_fields with
  | [], [] -> []
  | sf :: srest, tf :: trest ->
      let mismatches = ref [] in
      (* Check field name *)
      let name_ok = sf.irf_name = tf.irf_name in
      (* Check offset *)
      let offset_mismatch =
        if sf.irf_offset <> tf.irf_offset
        then [OffsetMismatch sf.irf_name sf.irf_offset tf.irf_offset]
        else []
      in
      (* Check size *)
      let size_mismatch =
        if sf.irf_size <> tf.irf_size
        then [TypeWidthMismatch sf.irf_name sf.irf_size tf.irf_size]
        else []
      in
      (* Check alignment *)
      let align_mismatch =
        if sf.irf_align <> tf.irf_align
        then [AlignmentMismatch sf.irf_name sf.irf_align tf.irf_align]
        else []
      in
      (* Check endianness for multi-byte fields *)
      let endian_mismatch =
        if sf.irf_size > 1 && needs_byte_swap source_endian target_endian
        then [EndiannessMismatch sf.irf_name source_endian target_endian]
        else []
      in
      offset_mismatch @ size_mismatch @ align_mismatch @ endian_mismatch @
      compare_fields srest trest source_endian target_endian
  | [], _ -> [FieldCountMismatch (List.Tot.length source_fields) (List.Tot.length target_fields)]
  | _, [] -> [FieldCountMismatch (List.Tot.length source_fields) (List.Tot.length target_fields)]

(* Main ABI compatibility check function.
   Compares source_struct (from caller) against target_struct (at callee).
   Returns list of all detected mismatches. *)
let check_abi_compatibility
    (source_struct: ir_struct)
    (target_struct: ir_struct)
    : list abi_mismatch =
  let mismatches = ref [] in

  (* Check total struct size *)
  let size_mismatch =
    if source_struct.irs_layout.li_size <> target_struct.irs_layout.li_size
    then [SizeMismatch source_struct.irs_layout.li_size target_struct.irs_layout.li_size]
    else []
  in

  (* Check field count *)
  let field_count_mismatch =
    let src_count = List.Tot.length source_struct.irs_fields in
    let tgt_count = List.Tot.length target_struct.irs_fields in
    if src_count <> tgt_count
    then [FieldCountMismatch src_count tgt_count]
    else []
  in

  (* Check individual fields *)
  let field_mismatches =
    compare_fields
      source_struct.irs_fields
      target_struct.irs_fields
      source_struct.irs_layout.li_endianness
      target_struct.irs_layout.li_endianness
  in

  size_mismatch @ field_count_mismatch @ field_mismatches

(* Check if two structs are ABI-compatible (no mismatches) *)
let is_abi_compatible (source: ir_struct) (target: ir_struct) : bool =
  match check_abi_compatibility source target with
  | [] -> true
  | _ -> false

(* Check compatibility and return critical mismatches only *)
let check_critical_abi_mismatches
    (source_struct: ir_struct)
    (target_struct: ir_struct)
    : list abi_mismatch =
  let all_mismatches = check_abi_compatibility source_struct target_struct in
  List.Tot.filter (fun m -> match mismatch_severity m with
                           | SeverityCritical -> true
                           | SeverityHigh -> true
                           | _ -> false) all_mismatches

(** ============================================================================
    CROSS-PLATFORM ABI CHECKING
    ============================================================================

    Functions to check struct compatibility across different platforms.
    This is essential for portable code and cross-compilation scenarios. *)

(* Check struct compatibility between two ABIs *)
let check_cross_platform_compatibility
    (name: string)
    (fields: list (string & ffi_safe_type))
    (source_abi: target_abi)
    (target_abi: target_abi)
    : list abi_mismatch =
  let source_struct = compute_struct_layout_for_abi name fields source_abi in
  let target_struct = compute_struct_layout_for_abi name fields target_abi in
  check_abi_compatibility source_struct target_struct

(* Check struct against multiple target ABIs and collect all mismatches *)
let rec check_against_all_targets
    (name: string)
    (fields: list (string & ffi_safe_type))
    (source_abi: target_abi)
    (target_abis: list target_abi)
    : list (target_abi & list abi_mismatch) =
  match target_abis with
  | [] -> []
  | abi :: rest ->
      let mismatches = check_cross_platform_compatibility name fields source_abi abi in
      (abi, mismatches) :: check_against_all_targets name fields source_abi rest

(* Common target ABIs for portable code verification *)
let common_target_abis : list target_abi =
  [abi_linux_x86_64; abi_windows_x86_64; abi_macos_x86_64;
   abi_macos_arm64; abi_linux_arm64; abi_wasm32]

(* Check portability across common platforms *)
let check_portability
    (name: string)
    (fields: list (string & ffi_safe_type))
    (source_abi: target_abi)
    : list (target_abi & list abi_mismatch) =
  check_against_all_targets name fields source_abi common_target_abis

(** ============================================================================
    BYTE ORDER CONVERSION TRACKING
    ============================================================================

    Track where byte order conversions are needed for cross-platform
    data exchange (network protocols, file formats, etc.). *)

(* Byte order conversion requirement *)
type byte_order_conversion =
  | BOCNone     : byte_order_conversion  (* No conversion needed *)
  | BOCSwap16   : byte_order_conversion  (* Swap 2-byte value *)
  | BOCSwap32   : byte_order_conversion  (* Swap 4-byte value *)
  | BOCSwap64   : byte_order_conversion  (* Swap 8-byte value *)
  | BOCSwap128  : byte_order_conversion  (* Swap 16-byte value *)

(* Get required byte order conversion for a field *)
let get_byte_order_conversion
    (source_endian: endianness)
    (target_endian: endianness)
    (field_size: nat)
    : byte_order_conversion =
  if not (needs_byte_swap source_endian target_endian) then BOCNone
  else match field_size with
       | 1 -> BOCNone
       | 2 -> BOCSwap16
       | 4 -> BOCSwap32
       | 8 -> BOCSwap64
       | 16 -> BOCSwap128
       | _ -> BOCNone  (* Unusual sizes: no standard swap *)

(* Generate byte order conversion requirements for struct *)
let rec get_struct_byte_conversions
    (source_endian: endianness)
    (target_endian: endianness)
    (fields: list ir_field)
    : list (string & byte_order_conversion) =
  match fields with
  | [] -> []
  | f :: rest ->
      let conv = get_byte_order_conversion source_endian target_endian f.irf_size in
      match conv with
      | BOCNone -> get_struct_byte_conversions source_endian target_endian rest
      | _ -> (f.irf_name, conv) ::
             get_struct_byte_conversions source_endian target_endian rest

(** ============================================================================
    ABI COMPATIBILITY PROOFS
    ============================================================================ *)

(* Lemma: struct layout under same ABI is consistent *)
val same_abi_same_layout : abi:target_abi -> name:string ->
                           fields:list (string & ffi_safe_type) ->
  Lemma (let s1 = compute_struct_layout_for_abi name fields abi in
         let s2 = compute_struct_layout_for_abi name fields abi in
         s1.irs_layout.li_size = s2.irs_layout.li_size)
let same_abi_same_layout abi name fields = ()

(* Lemma: is_abi_compatible is reflexive *)
val abi_compatible_reflexive : s:ir_struct ->
  Lemma (is_abi_compatible s s = true)
let abi_compatible_reflexive s = ()

(* Lemma: empty struct has size 0 (or minimum alignment) on any ABI *)
val empty_struct_zero_size : abi:target_abi ->
  Lemma (compute_struct_size_abi abi [] = 1)
let empty_struct_zero_size abi = ()

(* Lemma: packed struct has no padding between fields *)
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
let packed_struct_no_padding name f1_name f1_type f2_name f2_type abi = ()

(** ============================================================================
    EXAMPLE: WINDOWS VS LINUX 'LONG' SIZE DIFFERENCE
    ============================================================================

    Demonstrates the classic ABI mismatch between Windows (LLP64) and
    Linux (LP64) where 'long' has different sizes. *)

(* Example struct that exhibits the Windows/Linux long mismatch *)
let example_data_fields : list (string & ffi_safe_type) =
  [("x", FFIInt I32 Signed);     (* int: 4 bytes on both *)
   ("y", FFIInt I64 Signed)]     (* long long: 8 bytes on both *)

(* This struct would have different layout if we used C 'long':
   - Windows x64: int (4) + long (4) = 8 bytes
   - Linux x64:   int (4) + long (8) = 16 bytes (with padding)

   Using explicit I32/I64 avoids this issue. *)

(* Verify the example struct has same layout on Windows and Linux *)
val example_struct_portable : unit ->
  Lemma (let win = compute_struct_layout_for_abi "Data" example_data_fields abi_windows_x86_64 in
         let lin = compute_struct_layout_for_abi "Data" example_data_fields abi_linux_x86_64 in
         win.irs_layout.li_size = lin.irs_layout.li_size)
let example_struct_portable () = ()

(** ============================================================================
    FFI GUARD GENERATION FROM ABI CHECKS
    ============================================================================

    Generate runtime guards to verify ABI assumptions at FFI boundaries.
    These can be compiled to assertions or static_assert in generated code. *)

(* Guard type for runtime ABI verification *)
type abi_guard =
  | GuardSizeOf
      : type_name:string
      -> expected:nat
      -> abi_guard
      (* static_assert(sizeof(T) == expected) *)

  | GuardAlignOf
      : type_name:string
      -> expected:nat
      -> abi_guard
      (* static_assert(alignof(T) == expected) *)

  | GuardOffsetOf
      : type_name:string
      -> field_name:string
      -> expected:nat
      -> abi_guard
      (* static_assert(offsetof(T, field) == expected) *)

(* Generate guards for a struct layout *)
let rec generate_field_guards
    (struct_name: string)
    (fields: list ir_field)
    : list abi_guard =
  match fields with
  | [] -> []
  | f :: rest ->
      GuardOffsetOf struct_name f.irf_name f.irf_offset ::
      generate_field_guards struct_name rest

(* Generate all guards for a struct *)
let generate_struct_guards (s: ir_struct) : list abi_guard =
  [GuardSizeOf s.irs_name s.irs_layout.li_size;
   GuardAlignOf s.irs_name s.irs_layout.li_alignment] @
  generate_field_guards s.irs_name s.irs_fields

(* Convert guard to C static_assert string *)
let guard_to_c_assert (g: abi_guard) : string =
  match g with
  | GuardSizeOf ty exp ->
      "_Static_assert(sizeof(" ^ ty ^ ") == " ^ string_of_int exp ^
      ", \"ABI size mismatch for " ^ ty ^ "\");"
  | GuardAlignOf ty exp ->
      "_Static_assert(_Alignof(" ^ ty ^ ") == " ^ string_of_int exp ^
      ", \"ABI alignment mismatch for " ^ ty ^ "\");"
  | GuardOffsetOf ty field exp ->
      "_Static_assert(offsetof(" ^ ty ^ ", " ^ field ^ ") == " ^ string_of_int exp ^
      ", \"ABI offset mismatch for " ^ ty ^ "." ^ field ^ "\");"
