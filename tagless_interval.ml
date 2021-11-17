open Tagless_types

type _ c_type +=
  | CIntInterval: (int * int) c_type

module IntegerModulo_interval(Param: Tagless_fft.Ntt_param) = struct
  include Tagless_impl.R

  let domain_c_type = CIntInterval
  let max_uint16 = 65535
  let max_uint15 = 32767
  let max_uint14 = 16383

  let subtract_bias = 2 * Param.q
  let max_lhs = max_uint16 - subtract_bias
  (* let max_lhs = max_uint15 *)

  let two_pow16 = (Int.shift_left 1 16)

  type t = int * int

  let lift (itv: t) = fun () -> itv

  let one = (1, 1)

  let make_thunk x y = (fun () -> (x, y))

  let mulhi x y =
    let prod = x * y in
    Int.shift_right_logical prod 16

  let mullo x y =
    let prod = x * y in
    prod mod two_pow16

  let barret_reduce x =
    let mul_5 = mulhi x 5 in
    let rhs = (mullo mul_5 Param.q) in
    assert (x >= rhs);
    x - rhs

  let min_max_f f lo hi =
    assert (lo <= hi && 0 <= lo);
    let lo_reduced = f lo in
    let mn = ref lo_reduced in
    let mx = ref lo_reduced in
    for i = lo + 1 to hi do
      let reduced = f i in
      mn := min !mn reduced;
      mx := max !mx reduced;
    done;
    !mn, !mx

  let mullo_interval _ _ = 0, max_uint16

  let mulhi_interval (lo1, hi1) (lo2, hi2) =
    let lo_prod = lo1 * lo2 in
    let hi_prod = hi1 * hi2 in
    let lo, hi = Int.shift_right_logical lo_prod 16, Int.shift_right_logical hi_prod 16 in
    assert (lo <= hi);
    lo, hi

  let barret_reduce_interval lo hi =
    assert (lo <= hi && 0 <= lo && hi <= max_uint16);
    if true then
      let res = min_max_f barret_reduce lo hi in
      assert ((snd res) <= max_uint14);
      res
    else
      (* This does not work, the assert fails on new_hi <= max_uint14 *)
      let (-) (lo1, hi1) (lo2, hi2) = lo1 - hi2, hi1 - lo2 in
      let mul5 = mulhi_interval (lo, hi) (5, 5) in
      let new_lo, new_hi = (lo, hi) - (mullo_interval mul5 (Param.q, Param.q)) in
      assert (new_lo <= new_hi && 0 <= new_lo && new_hi <= max_uint14);
      new_lo, new_hi

  let add x y =
    let (lo1, hi1) = x () in
    let (lo2, hi2) = y () in
    (* Printf.printf "add input lhs: lo1 = %d, hi1 = %d\n" lo1 hi1; *)
    assert (lo1 <= hi1 && lo2 <= hi2);
    assert (hi1 <= max_lhs && hi2 < max_uint14);
    assert (hi1 + hi2 <= max_uint16);
    (* lazy reduction *)
    (* Printf.printf "add: lo = %d, hi = %d\n" (lo1 + lo2) (hi1 + hi2); *)
    make_thunk (lo1 + lo2) (hi1 + hi2)

  let sub x y =
    (* x: 14 or 15 bit
     * y: 14 bit *)
    let (lo1, hi1) = x () in
    let (lo2, hi2) = y () in
    (* Printf.printf "sub input: lo1 = %d, hi1 = %d, lo2 = %d, hi2 = %d\n" lo1 hi1 lo2 hi2; *)
    assert (lo1 <= hi1 && lo2 <= hi2);
    assert (hi1 <= max_lhs && hi2 < max_uint14);
    assert (hi2 <= subtract_bias);
    assert (hi1 + subtract_bias <= max_uint16);
    let lo, hi = barret_reduce_interval (lo1 + subtract_bias - hi2) (hi1 + subtract_bias - lo2) in
    (* Printf.printf "sub: hi1 + bias = %d, lo = %d, hi = %d\n" (hi1 + subtract_bias) lo hi; *)
    assert (lo <= hi);
    assert (hi <= max_uint14); (* max = 14743 *)
    make_thunk lo hi

  let csub_interval (lo, hi) =
    assert (hi < 2 * Param.q);
    let csub x =
      let tmp_sub = x - Param.q in
      let tmp_sra = Int.shift_right tmp_sub  63 in
      let tmp_and = tmp_sra land Param.q in
      tmp_sub + tmp_and
    in
    let res = min_max_f csub lo hi in
    assert ((snd res) < Param.q);
    res

  let mul_reduce_interval (lo1, hi1) (lo2, hi2) =
    let not_zero _ = (0, 1) in
    let (+) (lo1, hi1) (lo2, hi2) = lo1 + lo2, hi1 + hi2 in
    let mlo = mullo_interval (lo1, hi1) (lo2, hi2) in
    let mhi = mulhi_interval (lo1, hi1) (lo2, hi2) in
    let mlo_qinv = mullo_interval mlo (Param.qinv, Param.qinv) in
    let t = mulhi_interval mlo_qinv (Param.q, Param.q) in
    let carry = not_zero mlo in
    let res = mhi + t + carry in
    let res_csub = csub_interval res in
    (* let (lo1, hi1) = res in
     * let (lo2, hi2) = res_csub in
     * Printf.printf "before csub: lo = %d, hi = %d \n" lo1 hi1;
     * Printf.printf "after csub: lo = %d, hi = %d \n" lo2 hi2; *)
    res_csub

  let mul x y =
    let (lo1, hi1) = x () in
    let (lo2, hi2) = y () in
    assert (lo1 <= hi1 && lo2 <= hi2);
    (* Printf.printf "mul input, hi1 = %d, hi2 = %d\n" hi1 hi2; *)
    assert (hi1 <= max_lhs && hi2 < max_uint14);
    let lo, hi = mul_reduce_interval (lo1, hi1) (lo2, hi2) in
    assert (lo <= hi);
    assert (hi < max_uint14);
    make_thunk lo hi

  (* let mul _ _ = make_thunk 0 max_uint14 *)

  let primitive_root_power _ j =
    let open Tagless_fft in
    let module Prim_roots = Primitive_roots_int(Param)(struct let factor = two_pow16 end) in
    let w = Prim_roots.primitive_root_power Param.n j in
    w, w

  let barret_reduce itv =
    let lo, hi = itv () in
    (* if hi >= 39000 then
     *   Printf.printf "Doing barret reduce on lo = %d, hi = %d\n" lo hi; *)
    let new_lo, new_hi = barret_reduce_interval lo hi in
    (* Printf.printf "barret after lazy: lo = %d, hi = %d\n" new_lo new_hi; *)
    assert (new_hi <= max_uint14);
    make_thunk new_lo new_hi
end
