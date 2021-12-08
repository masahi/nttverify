open Tagless_types
open Tagless_vectorize


module Primitive_roots(D: Domain) = struct
  let powers_memory_efficient n =
    let num_stage = Base.Int.floor_log2 n in
    let powers = Array.make n D.one in
    let index = ref 0 in
    for s = 1 to num_stage do
      let m = Int.shift_left 1 s in
      let num_butterfly = Int.shift_right n s in
      for j = 0 to (m / 2 - 1) do
        powers.(!index) <- D.primitive_root_power n (j * num_butterfly);
        index := !index + 1;
      done;
    done;
    powers

  let powers_for_vectorized n vec_len =
    let num_stage = Base.Int.floor_log2 n in
    let size = ref 0 in
    for s = 1 to num_stage do
      let m = Int.shift_left 1 s in
      if (m / 2) < vec_len then
        size := !size + vec_len
      else
        size := !size + (m / 2)
    done;
    let powers = Array.make !size D.one in
    let coeff_begins = Array.make num_stage 0 in
    let index = ref 0 in
    for s = 1 to num_stage do
      coeff_begins.(s - 1) <- !index;
      let m = Int.shift_left 1 s in
      let num_butterfly = Int.shift_right n s in
      let index_before = !index in
      for j = 0 to (m / 2 - 1) do
        powers.(!index) <- D.primitive_root_power n (j * num_butterfly);
        index := !index + 1;
      done;
      if (m / 2) < vec_len then
        let num_repeat = vec_len / (m / 2) - 1 in
        for _ = 1 to num_repeat do
          for j = 0 to (m / 2 - 1) do
            powers.(!index) <- powers.(index_before + j);
            index := !index + 1;
          done;
        done
    done;
    powers, coeff_begins
end

module ComplexDomain(Lang: Complex_lang) = struct
  include Lang
  open Complex
  type t = Complex.t

  let lift = complex_
  let add = cadd

  let sub = csub

  let mul = cmul

  let one = {re = 1.0; im = 0.0 }

  let primitive_root_power n j =
    let re r = { re = r; im = 0.0 } in
    let pi = 3.14159265358979 in
    let i = Complex.i in
    let num = Complex.mul (re (-. 2. *. pi *. float j)) i in
    let den = re (float n) in
    Complex.exp (Complex.div num den)
end

module type Ntt_param = sig
  val n: int
  val q: int

  val qinv: int
  val omega: int
end

module Primitive_roots_int(Param: Ntt_param)(F: sig val factor: int end) = struct
  let one = 1
  let mul_ x y = (x * y) mod Param.q

  let primitive_root_power _ j =
    let rec power i acc =
      if i = 0 then mul_ acc F.factor
      else
        let update = mul_ acc Param.omega in
        power (i - 1) update
    in
    power j 1
end

module IntegerModulo(Base_lang: Int_modulo_lang)(Param: Ntt_param) = struct
  include Base_lang
  type t = int

  let domain_c_type = CInt

  let q = Param.q
  let omega = Param.omega

  let lift = int_
  let add x y = mod_ (x %+ y) q
  let sub x y =
    let bias = int_ (q * 3) in
    mod_ ((x %+ bias) %- y) q

  let mul x y = mod_ (x %* y) q

  include Primitive_roots_int(Param)(struct let factor = 1 end)
end

module IntegerModulo_lazy(Base_lang: Int_lang_for_reduction)(Param: Ntt_param) = struct
  include Base_lang
  type t = int

  let domain_c_type = CInt
  let rlog = 16
  let q = Param.q
  let r = (Int.shift_left 1 rlog)

  let lift = int_

  let one = 1

  let csub x =
    let tmp_sub = x %- (int_ q) in
    let tmp_sra = tmp_sub %>> (int_ 63) in
    let tmp_and = tmp_sra %& (int_ q) in
    tmp_sub %+ tmp_and

  let barret_reduce x =
    let mul_5 = mulhi x (int_ 5) in
    x %- (mullo mul_5 (int_ q))

  let add x y =
    (x %+ y)

  let sub x y =
    let bias = int_ (2 * q) in
    barret_reduce ((x %+ bias) %- y)

  let mul x y =
    let mlo = mullo x y in
    let mhi = mulhi x y in
    let mlo_qinv = mullo mlo (int_ Param.qinv) in
    let t = mulhi mlo_qinv (int_ Param.q) in
    let carry = not_zero mlo in
    let res = mhi %+ t %+ carry in
    csub res

  let primitive_root_power _ j =
    let module Prim_roots = Primitive_roots_int(Param)(struct let factor = r end) in
    Prim_roots.primitive_root_power Param.n j

end

module UIntegerModulo(Base_lang: C_lang_aux)(Param: Ntt_param) = struct
  include Base_lang
  type t = Base_lang.uint16
  let domain_c_type = CUInt16

  let q = Param.q
  let qinv = Param.qinv

  let rlog = 16
  let r = (Int.shift_left 1 rlog)

  let csub = func "csub" CUInt16 (fun (a: UInt16.t expr) ->
      let open Int16 in
      let q = lift (Signed.Int32.of_int q) in
      let a_i16 = UInt16.to_int16 a in
      let_ (a_i16 %- q) (fun a ->
          return_ (to_uint16 (a %+ ((a %>> 15) %& q)))))

  let barret_reduce = func "barret_reduce" CUInt16 (fun (a: UInt16.t expr) ->
      let open UInt32 in
      let five = lift (Unsigned.UInt32.of_int 5) in
      let q = lift (Unsigned.UInt32.of_int q) in
      let a_u32 = UInt16.to_uint32 a in
      let_ ((a_u32 %* five) %>> 16) (fun u ->
          let_ (UInt16.(%-) a (to_uint16 (u %* q))) (fun a ->
              return_ a)))

  let montgomery_reduce = func "montgomery_reduce" CUInt32 (fun (a: UInt32.t expr) ->
      let open UInt32 in
      let r_minus_one = lift (Unsigned.UInt32.of_int (r - 1)) in
      let q = lift (Unsigned.UInt32.of_int q) in
      let qinv = lift (Unsigned.UInt32.of_int qinv) in
      let_ (a %& r_minus_one %* qinv) (fun u ->
          let_ (u %& r_minus_one) (fun u ->
              let_ (u %* q) (fun u ->
                  let_ (a %+ u) (fun a ->
                      let_ (a %>> rlog) (fun t ->
                          return_ (app csub (to_uint16 t))))))))

  let lift = Base_lang.UInt16.lift

  let add x y =
    let open UInt16 in
    app barret_reduce (x %+ y)

  let sub x y =
    let open UInt16 in
    let bias = lift (Unsigned.UInt16.of_int (q * 2)) in
    app barret_reduce ((x %+ bias) %- y)

  let mul x y =
    let open UInt32 in
    app montgomery_reduce ((UInt16.to_uint32 x) %* (UInt16.to_uint32 y))

  let one = Unsigned.UInt16.of_int 1

  let primitive_root_power _ j =
    let module Prim_roots = Primitive_roots_int(Param)(struct let factor = r end) in
    Unsigned.UInt16.of_int (Prim_roots.primitive_root_power Param.n j)

end

module UIntegerModulo_lazy(Base_lang: C_lang_aux)(Param: Ntt_param) = struct
  include UIntegerModulo(Base_lang)(Param)

  let add x y =
    let open UInt16 in
    (x %+ y)

  let barret_reduce x = app barret_reduce x

end

module Bit_rev(S: Array_lang) = struct
  open S

  let bit_reverse tbl in_ty =
    let len = Array.length tbl in
    func "bit_reverse" in_ty (fun arr ->
        let table = arr_init len (fun i -> int_ (tbl.(i))) in
        for_ (int_ 0) (int_ len) (int_ 1) (fun i ->
            let r = arr_get table i in
            if_ (i %< r)
              (let_ (arr_get arr i) (fun tmp ->
                   seq
                     (arr_set arr i (arr_get arr r))
                     (arr_set arr r tmp)
                 ))
              None
          )
      )

  let get_bit_reverse n in_ty =
    let bit_reverse_1024 () =
      bit_reverse Bit_reverse.Bit_rev_1024.bit_reverse_table in_ty in
    let bit_reverse_8 () =
      bit_reverse Bit_reverse.Bit_rev_8.bit_reverse_table in_ty in
    let bit_reverse_4 () =
      bit_reverse Bit_reverse.Bit_rev_4.bit_reverse_table in_ty in
    let bit_reverse_2 () =
      bit_reverse Bit_reverse.Bit_rev_2.bit_reverse_table in_ty in
    let funcs = [(2, bit_reverse_2); (4, bit_reverse_4); (8, bit_reverse_8); (1024, bit_reverse_1024)] in
    List.assoc n funcs

end


module FFT_lazy_gen(Lang: Array_lang)(D: Domain_with_barret with type 'a expr = 'a Lang.expr) = struct
  open Lang
  open Sugar(Lang)

  module Lazy_reduction(Stage: sig val s: int end) = struct
    module D = struct
      include D
      let add x y =
        let res = D.add x y in
        if Stage.s mod 3 = 0 then begin
          barret_reduce res
        end
        else res

      let sub x y = D.sub x y
    end
  end

  let fft n =
    let module B_rev = Bit_rev(Lang) in
    let module Prim_roots = Primitive_roots(D) in
    let prim_root_powers = Prim_roots.powers_memory_efficient n in
    let prim_root_powers = arr_init n (fun i -> D.lift (prim_root_powers.(i))) in
    let input_arr_ty = CArr (D.domain_c_type) in
    let bit_reverse = B_rev.get_bit_reverse n input_arr_ty () in
    let num_stage = Base.Int.floor_log2 n in
    let n = int_ n in
    let fft_stage s =
      let fname = Printf.sprintf "fft%d" s in
      func fname input_arr_ty (fun input ->
          let2
            (one %<< (int_ s))
            ((one %<< ((int_ s) %- one)) %- one)
            (fun m coeff_begin ->
               let m_half = (m %/ two) in
               for_ zero n m (fun k ->
                   for_ zero m_half one (fun j ->
                       let open Lazy_reduction(struct let s = s end) in
                       let index = k %+ j in
                       let omega = arr_get prim_root_powers (coeff_begin %+ j) in
                       let2
                         (arr_get input index)
                         (D.mul (arr_get input (index %+ m_half)) omega)
                         (fun u t ->
                            seq
                              (arr_set input index (D.add u t))
                              (arr_set input (index %+ m_half) (D.sub u t))))))) in
    func "fft" input_arr_ty (fun input ->
        seq
          (call bit_reverse input)
          (unroll 1 (num_stage + 1) (fun s ->
               (call (fft_stage s) input))))
end


module FFT_vectorized_with_shuffle_gen
    (Lang: Array_lang)
    (D: Domain with type 'a expr = 'a Lang.expr)
    (V_lang: Vector_lang_with_shuffle_with_barret
     with type 'a expr = 'a Lang.expr
     with type 'a stmt = 'a Lang.stmt
     with type Vector_domain.t = D.t) =
struct
  open Lang
  open Sugar(Lang)

  module Inner_loop(L: Vec with type 'a expr = 'a Lang.expr with type 'a stmt = 'a Lang.stmt) = struct
    let fft_inner input m_half k prim_root_powers coeff_begin =
      let open L in
      for_ (int_ 0) m_half (int_ 1) (fun j ->
          let index = k %+ j in
          let omega = arr_get prim_root_powers (coeff_begin %+ j) in
          let2
            (D.mul (arr_get input (index %+ m_half)) omega)
            (arr_get input index)
            (fun t u ->
               seq
                 (arr_set input index (D.add u t))
                 (arr_set input (index %+ m_half) (D.sub u t))))
  end

  module Lazy_reduction(V: Vector_lang_with_shuffle_with_barret)(Stage: sig val s: int end) : Vector_lang_with_shuffle
    with type 'a expr = 'a V.expr
    with type 'a stmt = 'a V.stmt
    with type Vector_domain.t = V.Vector_domain.t =
  struct
    include V

    module Vector_domain = struct
      include V.Vector_domain

      let vadd v0 v1 =
        let res = V.Vector_domain.vadd v0 v1 in
        if Stage.s mod 3 == 0 then barret_reduce res
        else res

      let vsub = V.Vector_domain.vsub
    end
  end

  let fft n =
    let module B_rev = Bit_rev(Lang) in
    let module Prim_roots = Primitive_roots(D) in
    let prim_root_powers, coeff_begins = Prim_roots.powers_for_vectorized n V_lang.vec_len in
    let prim_root_powers = arr_init (Array.length prim_root_powers) (fun i -> D.lift (prim_root_powers.(i))) in
    let input_ty = CArr (D.domain_c_type) in
    let fft_stage s =
      let coeff_begin = int_ coeff_begins.(s - 1) in
      let m = (Int.shift_left 1 s) in
      let m_half = int_ (m / 2) in
      let no_shuffle = (m / 2) >= V_lang.vec_len in
      let fname = Printf.sprintf "fft%d" s in
      let module V_lang_lazy = Lazy_reduction(V_lang)(struct let s = s end) in
      func fname input_ty (fun input ->
          if no_shuffle then
            let module Inner_V = Inner_loop(Vectorize(V_lang_lazy)) in
            for_ zero (int_ n) (int_ m) (fun k ->
                Inner_V.fft_inner input m_half k prim_root_powers coeff_begin)
          else
            let open V_lang_lazy in
            let open V_lang_lazy.Vector_domain in
            let_ (vload prim_root_powers coeff_begin) (fun coeff ->
                for_ zero (int_ n) (int_ (vec_len * 2)) (fun k ->
                    let_ (vload input k) (fun v0 ->
                    let_ (vload input (k %+ (int_ vec_len))) (fun v1 ->
                    let2_ (shuffle s v0 v1) (fun v_lo v_hi ->
                    let_ (vmul v_hi coeff) (fun v_mul ->
                    let_ (vadd v_lo v_mul) (fun tmp_add ->
                    let_ (vsub v_lo v_mul) (fun tmp_sub ->
                    let2_ (shuffle s tmp_add tmp_sub) (fun v0_res v1_res ->
                       seq
                         (vstore input k v0_res)
                         (vstore input (k %+ (int_ vec_len)) v1_res)))))))))))
    in
    let num_stage = Base.Int.floor_log2 n in
    let bit_reverse = B_rev.get_bit_reverse n input_ty () in
    let fft_funcs = Array.init num_stage (fun s -> fft_stage (s + 1)) in
    func "fft" input_ty (fun input ->
        seq
          (call bit_reverse input)
          (unroll 1 (num_stage + 1) (fun s ->
               (call fft_funcs.(s - 1) input))))
end
