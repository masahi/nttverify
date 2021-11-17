open Tagless_impl_c
open Tagless_types
open Printf

module type Elem_ty = sig
  type t
  val of_int: int -> t
  val to_int: t -> int
  val rep_c_type: t c_type
end

module type SIMD_Instr = sig
  type 'a expr

  module T: Elem_ty

  type t = T.t
  type n

  val vec_len_exponent: n nat

  val broadcast: t -> (t, n) vec expr

  val add: (t, n) vec expr -> (t, n) vec expr -> (t, n) vec expr
  val sub: (t, n) vec expr -> (t, n) vec expr -> (t, n) vec expr
  val mullo: (t, n) vec expr -> (t, n) vec expr -> (t, n) vec expr
  val mulhi: (t, n) vec expr -> (t, n) vec expr -> (t, n) vec expr

  val bitwise_and: (t, n) vec expr -> (t, n) vec expr -> (t, n) vec expr
  val shift_right_a: (t, n) vec expr -> int -> (t, n) vec expr

  val not_zero: (t, n) vec expr -> (t, n) vec expr

  module Infix: sig
    val (%+): (t, n) vec expr -> (t, n) vec expr -> (t, n) vec expr
    val (%-): (t, n) vec expr -> (t, n) vec expr -> (t, n) vec expr
    val (%&): (t, n) vec expr -> (t, n) vec expr -> (t, n) vec expr
    val (%>>): (t, n) vec expr -> int -> (t, n) vec expr
  end
end

module Integer_modulo_SIMD
    (Base_lang: C_lang_aux)
    (Instr: SIMD_Instr with type 'a expr = 'a Base_lang.expr)
    (Param: Tagless_fft.Ntt_param) = struct
  open Base_lang
  type t = Instr.t
  type 'a expr = 'a Base_lang.expr
  (* representation of vector with 2^n elements *)
  type 'a vec = ('a, Instr.n) Tagless_types.vec

  open Instr
  open Infix

  let csub =
    let in_ty = CVec (Instr.T.rep_c_type, Instr.vec_len_exponent) in
    func "csub_vec" in_ty (fun v ->
        let vec_q = broadcast (T.of_int Param.q) in
        let_ (v %- vec_q) (fun tmp_sub ->
            let tmp_sra = shift_right_a tmp_sub 15 in
            let tmp_and = tmp_sra %& vec_q in
            return_ (add tmp_sub tmp_and)))

  let barret_reduce =
    let in_ty = CVec (Instr.T.rep_c_type, Instr.vec_len_exponent) in
    func "barret_reduce_vec" in_ty (fun v ->
        let vec_5 = broadcast (T.of_int 5) in
        let v_1 = mulhi v vec_5 in
        let vec_q = broadcast (T.of_int Param.q) in
        return_ (v %- (mullo v_1 vec_q)))

  let vadd: t vec expr -> t vec expr-> t vec expr = fun v1 v2 ->
    let in_ty = CVec (Instr.T.rep_c_type, Instr.vec_len_exponent) in
    let f =  func2 "vadd" in_ty in_ty (fun v1 v2 ->
        return_ (v1 %+ v2))
    in
    app2 f v1 v2

  let vsub v1 v2 =
    let in_ty = CVec (Instr.T.rep_c_type, Instr.vec_len_exponent) in
    let f = func2 "vsub" in_ty in_ty (fun v1 v2 ->
        let bias = broadcast (T.of_int (Param.q * 2)) in
        return_ (app barret_reduce ((v1 %+ bias) %- v2)))
    in
    app2 f v1 v2

  let vmul: t vec expr -> t vec expr -> t vec expr = fun v1 v2 ->
    let in_ty = CVec (Instr.T.rep_c_type, Instr.vec_len_exponent) in
    let f = func2 "vmul" in_ty in_ty (fun v1 v2 ->
        let_ (mullo v1 v2) (fun mlo ->
        let_ (mulhi v1 v2) (fun mhi ->
        let_ (broadcast (T.of_int Param.q)) (fun vec_q ->
        let_ (broadcast (T.of_int Param.qinv)) (fun vec_qinv ->
        let_ (mullo mlo vec_qinv) (fun mlo_qinv ->
        let_ (mulhi mlo_qinv vec_q) (fun t ->
        let_ (not_zero mlo) (fun carry ->
        let_ (mhi %+ t %+ carry) (fun res ->
        return_ (app csub res))))))))))
    in
    app2 f v1 v2

  let barret_reduce: t vec expr -> t vec expr = fun v ->
    app barret_reduce v
end

module type SIMD_str = sig
  val add: string
  val sub: string
  val mullo: string
  val mulhi: string
  val broadcast: string
  val shift_right_a: string
  val bitwise_and: string
  val not_zero: string -> string
end

module type Length_spec = sig
  type n
  val vec_len_exponent: n nat
end

module Make_SIMD_Instr(T: Elem_ty)(Instr: SIMD_str)(L: Length_spec) = struct
  type 'a expr = 'a c_type * string
  type n = L.n
  type t = T.t

  module T = T
  let vec_len_exponent = L.vec_len_exponent

  let broadcast: t -> (t, n) vec expr = fun s ->
    CVec (T.rep_c_type, L.vec_len_exponent), sprintf "%s(%d)" Instr.broadcast (T.to_int s)

  let binop: string -> (t, n) vec expr -> (t, n) vec expr-> (t, n) vec expr = fun op (ty1, v1) (ty2, v2) ->
    match ty1, ty2 with
    | CVec(_, _), CVec(_, _) ->
      (ty1, sprintf "%s(%s, %s)" op v1 v2)
    | _ -> assert false

  let add = binop Instr.add
  let sub = binop Instr.sub
  let mullo = binop Instr.mullo
  let mulhi = binop Instr.mulhi

  let bitwise_and = binop Instr.bitwise_and

  let shift_right: string -> (t, n) vec expr -> int -> (t, n) vec expr = fun op (ty1, v1) i ->
    match ty1 with
    | CVec(_, _) ->
      (ty1, sprintf "%s(%s, %d)" op v1 i)
    | _ -> assert false

  let shift_right_a = shift_right Instr.shift_right_a

  let not_zero: (t, n) vec expr -> (t, n) vec expr = fun (ty, v) ->
    match ty with
    | CVec(_, _) ->
      CVec (T.rep_c_type, vec_len_exponent), Instr.not_zero v
    | _ -> assert false

  module Infix = struct
    let (%+) = add
    let (%-) = sub
    let (%&) = bitwise_and
    let (%>>) = shift_right_a
  end

end

module Shuffle = struct
  module type SIMD_Instr_with_shuffle = sig
    include SIMD_Instr
    val shuffle: int -> (t, n) vec expr -> (t, n) vec expr -> ((t, n) vec expr * (t, n) vec expr)

  end

  module Integer_modulo_SIMD_with_shuffle
      (Base_lang: C_lang_aux)
      (Instr: SIMD_Instr_with_shuffle with type 'a expr = 'a Base_lang.expr)
      (Param: Tagless_fft.Ntt_param) = struct

    include Integer_modulo_SIMD(Base_lang)(Instr)(Param)

    let shuffle: int -> t vec expr -> t vec expr -> (t vec expr * t vec expr) = fun n v1 v2 ->
      Instr.shuffle n v1 v2
  end

  module type SIMD_str_with_shuffle = sig
    include SIMD_str
    val shuffle: int -> string -> string -> (string * string)
  end

  module Make_SIMD_Instr_with_shuffle(T: Elem_ty)(Instr: SIMD_str_with_shuffle)(L: Length_spec) = struct
    include Make_SIMD_Instr(T)(Instr)(L)
    let shuffle: int -> (t, n) vec expr -> (t, n) vec expr -> ((t, n) vec expr * (t, n) vec expr) = fun n (ty0, v0) (_, v1) ->
      let (v_lo, v_hi) = Instr.shuffle n v0 v1 in
      (ty0, v_lo), (ty0, v_hi)
  end
end

module U16 = struct
  type t = Unsigned.UInt16.t
  let of_int = Unsigned.UInt16.of_int
  let to_int = Unsigned.UInt16.to_int
  let rep_c_type = CUInt16
end


module AVX2_v16_Instr : SIMD_str = struct
  let add = "_mm256_add_epi16"
  let sub = "_mm256_sub_epi16"
  let mullo = "_mm256_mullo_epi16"
  let mulhi = "_mm256_mulhi_epu16"
  let broadcast = "_mm256_set1_epi16"
  let shift_right_a = "_mm256_srai_epi16"
  let bitwise_and = "_mm256_and_si256"
  let not_zero v =
    sprintf "_mm256_add_epi16(_mm256_cmpeq_epi16(%s, _mm256_set1_epi16(0)), _mm256_set1_epi16(1))" v

end

module AVX2_v16_Instr_with_shuffle : Shuffle.SIMD_str_with_shuffle = struct
  include AVX2_v16_Instr
  let shuffle1 v0 v1 =
    let v1_left_shift = sprintf "_mm256_slli_epi32(%s, 16)" v1 in
    let v0_right_shift = sprintf "_mm256_srli_epi32(%s, 16)" v0 in
    let v_lo = sprintf "_mm256_blend_epi16(%s, %s, 0xAA)" v0 v1_left_shift in
    let v_hi = sprintf "_mm256_blend_epi16(%s, %s, 0xAA)" v0_right_shift v1 in
    v_lo, v_hi

  let shuffle2 v0 v1 =
    let v1_left_shift = sprintf "_mm256_slli_epi64(%s, 32)" v1 in
    let v0_right_shift = sprintf "_mm256_srli_epi64(%s, 32)" v0 in
    let v_lo = sprintf "_mm256_blend_epi32(%s, %s, 0xAA)" v0 v1_left_shift in
    let v_hi = sprintf "_mm256_blend_epi32(%s, %s, 0xAA)" v0_right_shift v1 in
    v_lo, v_hi

  let shuffle3 v0 v1 =
    let v_lo = sprintf "_mm256_unpacklo_epi64(%s, %s)" v0 v1 in
    let v_hi = sprintf "_mm256_unpackhi_epi64(%s, %s)" v0 v1 in
    v_lo, v_hi

  let shuffle4 v0 v1 =
    let v_lo = sprintf "_mm256_permute2x128_si256(%s, %s, 0x20)" v0 v1 in
    let v_hi = sprintf "_mm256_permute2x128_si256(%s, %s, 0x31)" v0 v1 in
    v_lo, v_hi

  let shuffle n v0 v1 = match n with
    | 1 -> shuffle1 v0 v1
    | 2 -> shuffle2 v0 v1
    | 3 -> shuffle3 v0 v1
    | 4 -> shuffle4 v0 v1
    | _ -> assert false
end

module AVX2_v16_length_spec = struct
  type n = z s s s s
  let vec_len_exponent = S (S (S (S Z)))
end

module AVX2_UInt16_int_modulo_with_shuffle(Scalar_domain: Domain)(Param: Tagless_fft.Ntt_param) = struct
  open Shuffle
  module SIMD_v16_u16 = Make_SIMD_Instr_with_shuffle(U16)(AVX2_v16_Instr_with_shuffle)(AVX2_v16_length_spec)
  module Vector_domain = Integer_modulo_SIMD_with_shuffle(C_codegen)(SIMD_v16_u16)(Param)
  type 'a vec = 'a Vector_domain.vec

  include C_codegen

  type t = Scalar_domain.t

  let vec_len = 16

  module Mem = struct
    type t = Scalar_domain.t
    type n = SIMD_v16_u16.n

    let vec_len_exponent = SIMD_v16_u16.vec_len_exponent

    let vload = "_mm256_loadu_si256"
    let vstore = "_mm256_storeu_si256"
  end

  module M = SIMD_Mem(Mem)

  let vload = M.vload
  let vstore = M.vstore

  let shuffle = SIMD_v16_u16.shuffle

  let barret_reduce = Vector_domain.barret_reduce
end

module AVX512_v32_length_spec = struct
  type n = z s s s s s
  let vec_len_exponent = S (S (S (S (S Z))))
end

module AVX512_v32_Instr : SIMD_str = struct
  let add = "_mm512_add_epi16"
  let sub = "_mm512_sub_epi16"
  let mullo = "_mm512_mullo_epi16"
  let mulhi = "_mm512_mulhi_epu16"
  let broadcast = "_mm512_set1_epi16"
  let shift_right_a = "_mm512_srai_epi16"
  let bitwise_and = "_mm512_and_si512"
  let not_zero v = sprintf "_mm512_add_epi16(_mm512_movm_epi16(_mm512_cmpeq_epi16_mask(%s, _mm512_set1_epi16(0))), _mm512_set1_epi16(1))" v
end

module AVX512_v32_Instr_with_shuffle : Shuffle.SIMD_str_with_shuffle = struct
  include AVX512_v32_Instr
  let shuffle1 v0 v1 =
    let v1_left_shift = sprintf "_mm512_slli_epi32(%s, 16)" v1 in
    let v0_right_shift = sprintf "_mm512_srli_epi32(%s, 16)" v0 in
    let v_lo = sprintf "_mm512_mask_blend_epi16(_cvtu32_mask32(0xAAAAAAAA), %s, %s)" v0 v1_left_shift in
    let v_hi = sprintf "_mm512_mask_blend_epi16(_cvtu32_mask32(0xAAAAAAAA), %s, %s)" v0_right_shift v1 in
    v_lo, v_hi

  let shuffle2 v0 v1 =
    let v1_left_shift = sprintf "_mm512_slli_epi64(%s, 32)" v1 in
    let v0_right_shift = sprintf "_mm512_srli_epi64(%s, 32)" v0 in
    let v_lo = sprintf "_mm512_mask_blend_epi32(_cvtu32_mask16(0xAAAA), %s, %s)" v0 v1_left_shift in
    let v_hi = sprintf "_mm512_mask_blend_epi32(_cvtu32_mask16(0xAAAA), %s, %s)" v0_right_shift v1 in
    v_lo, v_hi

  let shuffle3 v0 v1 =
    let v_lo = sprintf "_mm512_unpacklo_epi64(%s, %s)" v0 v1 in
    let v_hi = sprintf "_mm512_unpackhi_epi64(%s, %s)" v0 v1 in
    v_lo, v_hi

  let shuffle4 v0 v1 =
    (* 1x8 0x8 1x8 0x8*)
    let idx1 = "_mm512_set_epi16(55, 54, 53, 52, 51, 50, 49, 48, 23, 22, 21, 20, 19, 18, 17, 16, 39, 38, 37, 36, 35, 34, 33, 32, 7, 6, 5, 4, 3, 2, 1, 0)" in
    let idx2 = "_mm512_set_epi16(63, 62, 61, 60, 59, 58, 57, 56, 31, 30, 29, 28, 27, 26, 25, 24, 47, 46, 45, 44, 43, 42, 41, 40, 15, 14, 13, 12, 11, 10, 9, 8)" in
    let v_lo = sprintf "_mm512_permutex2var_epi16(%s, %s, %s)" v0 idx1 v1 in
    let v_hi = sprintf "_mm512_permutex2var_epi16(%s, %s, %s)" v0 idx2 v1 in

    v_lo, v_hi

  let shuffle5 v0 v1 =
    let idx1 = "_mm512_set_epi16(47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0)" in
    let idx2 = "_mm512_set_epi16(63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16)" in
    let v_lo = sprintf "_mm512_permutex2var_epi16(%s, %s, %s)" v0 idx1 v1 in
    let v_hi = sprintf "_mm512_permutex2var_epi16(%s, %s, %s)" v0 idx2 v1 in
    v_lo, v_hi

  let shuffle n v0 v1 = match n with
    | 1 -> shuffle1 v0 v1
    | 2 -> shuffle2 v0 v1
    | 3 -> shuffle3 v0 v1
    | 4 -> shuffle4 v0 v1
    | 5 -> shuffle5 v0 v1
    | _ -> assert false
end

module AVX512_UInt16_int_modulo_with_shuffle(Scalar_domain: Domain)(Param: Tagless_fft.Ntt_param) = struct
  open Shuffle
  module SIMD_v32_u16 = Make_SIMD_Instr_with_shuffle(U16)(AVX512_v32_Instr_with_shuffle)(AVX512_v32_length_spec)
  module Vector_domain = Integer_modulo_SIMD_with_shuffle(C_codegen)(SIMD_v32_u16)(Param)
  type 'a vec = 'a Vector_domain.vec

  include C_codegen
  type t = Scalar_domain.t
  let vec_len = 32

  module Mem = struct
    type t = Scalar_domain.t
    type n = SIMD_v32_u16.n
    let vec_len_exponent = SIMD_v32_u16.vec_len_exponent
    let vload = "_mm512_loadu_si512"
    let vstore = "_mm512_storeu_si512"
  end

  module M = SIMD_Mem(Mem)

  let vload = M.vload
  let vstore = M.vstore
  let shuffle = SIMD_v32_u16.shuffle
  let barret_reduce = Vector_domain.barret_reduce
end
